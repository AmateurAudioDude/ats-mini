// FM-DX Webserver tuner protocol for the ATS Mini, ported from:
//   FM-DX Tuner, Copyright (C) 2023-2025 Konrad Kosmatka
//   FM-DX Tuner SI47XX support and driver, Copyright (c) 2026 Mark de Bruijn (bkram)
// SPDX-License-Identifier: GPL-3.0-or-later

#include "Common.h"
#include "Menu.h"
#include "Utils.h"
#include "Storage.h"
#include "FmdxMode.h"
#include <Wire.h>

#define FMDX_QUALITY_INTERVAL    66 // Default signal report interval (ms)
#define FMDX_RDS_INTERVAL        90 // RDS FIFO poll interval (ms)
#define FMDX_SCAN_SETTLE          5 // Minimum time from a scan tune to its signal reading (ms)
#define FMDX_CTS_TIMEOUT        150 // Receiver ready timeout (ms)
#define FMDX_STC_TIMEOUT        250 // Tune complete timeout (ms)
#define FMDX_DISCONNECT_TIME   1000 // Sustained USB disconnect that ends the session (ms)
#define FMDX_STALL_TIME       10000 // Host not reading for this long ends the session (ms)
#define FMDX_STALL_FREE          64 // Free transmit space below which the host is not reading

// SI4732 commands the spectrum scan sends directly
#define CMD_FM_TUNE_FREQ   0x20
#define CMD_FM_TUNE_STATUS 0x22
#define CMD_FM_RSQ_STATUS  0x23
#define CMD_AM_TUNE_FREQ   0x40
#define CMD_AM_TUNE_STATUS 0x42
#define CMD_AM_RSQ_STATUS  0x43

static bool active = false; // Session started by the webserver

static char cmdLine[64];
static uint8_t cmdLength = 0;

static uint32_t qualityInterval = FMDX_QUALITY_INTERVAL;
static uint32_t lastQuality = 0;
static uint32_t lastRds = 0;
static uint32_t alignment = 0;
static bool stereoOutput = true;

static uint32_t reportedHz = 0;
static uint8_t reportedMode = FM;

static uint32_t scanFrom = 0;
static uint32_t scanTo = 0;
static uint32_t scanStep = 0;
static uint32_t scanBandwidth = 0;

static bool disconnectPending = false;
static uint32_t disconnectedAt = 0;
static bool stalled = false;
static uint32_t stalledAt = 0;

// Receiver settings the webserver changes
struct Settings
{
  uint8_t volume;
  uint8_t region;
  uint8_t stereo;
  uint8_t squelch;
  int8_t fmAgc;
  int8_t amAgc;
  int8_t ssbAgc;
  uint8_t mode[64];
  int8_t step[64];
  int8_t bandwidth[64];
  bool muted;
};

// Before the session, and as the webserver last set them. When the session
// ends, settings the user has not changed since go back to their earlier values.
static Settings saved, applied;

// Recent PI codes, rating how often each has been confirmed
static uint16_t piHistory[64];
static uint64_t piErrors = 0;
static uint8_t piFill = 0;
static uint8_t piPos = 63;

// Protocol modes: FM-DX Tuner defines 0 = FM and 1 = AM, this receiver adds 2 = LSB and 3 = USB
static const uint8_t protocolModes[] = { FM, AM, LSB, USB };

// AM filters: width, receiver filter, and position in the AM bandwidth menu
static const struct
{
  uint16_t hz;
  uint8_t filter;
  uint8_t menu;
} amWidths[] =
{
  { 1000, 4, 0 }, { 1800, 5, 1 }, { 2000, 3, 2 }, { 2500, 6, 3 },
  { 3000, 2, 4 }, { 4000, 1, 5 }, { 6000, 0, 6 },
};

// SSB filters: width and position in the SSB bandwidth menu
static const struct
{
  uint16_t hz;
  uint8_t menu;
} ssbWidths[] =
{
  { 500, 0 }, { 1000, 1 }, { 1200, 2 }, { 2200, 3 }, { 3000, 4 }, { 4000, 5 },
};

static uint8_t protocolMode(uint8_t mode)
{
  for(uint8_t i = 0; i < ITEM_COUNT(protocolModes); i++)
    if(protocolModes[i] == mode) return(i);
  return(0);
}

static uint32_t bandMinKhz(int band) { return(bands[band].minimumFreq / 1000); }
static uint32_t bandMaxKhz(int band) { return(bands[band].maximumFreq / 1000); }
static uint32_t bandSpan(int band) { return(bands[band].maximumFreq - bands[band].minimumFreq); }

static bool covers(int band, uint32_t fromKhz, uint32_t toKhz)
{
  return(bandMinKhz(band) <= fromKhz && toKhz <= bandMaxKhz(band));
}

// Widest band in the mode, or in any HF mode, that covers the range (any band when toKhz is 0)
static int widestBand(uint8_t mode, bool anyHf = false, uint32_t fromKhz = 0, uint32_t toKhz = 0)
{
  int best = -1;
  for(int i = 0; i < getTotalBands(); i++)
  {
    const bool match = anyHf ? bands[i].bandMode != FM : bands[i].bandMode == mode;
    if(!match || (toKhz && !covers(i, fromKhz, toKhz))) continue;
    if(best < 0 || bandSpan(i) > bandSpan(best)) best = i;
  }
  return(best);
}

// The current band when it covers the range, otherwise the widest band of the mode that does
static int bandFor(uint8_t mode, uint32_t fromKhz, uint32_t toKhz)
{
  if(currentMode == mode && covers(bandIdx, fromKhz, toKhz)) return(bandIdx);
  return(widestBand(mode, false, fromKhz, toKhz));
}

// HF modes can use any HF band: the current one, one already in the mode, or the widest
static int hfBandFor(uint8_t mode, uint32_t fromKhz, uint32_t toKhz)
{
  if(currentMode != FM && covers(bandIdx, fromKhz, toKhz)) return(bandIdx);
  const int band = widestBand(mode, false, fromKhz, toKhz);
  return(band >= 0 ? band : widestBand(mode, true, fromKhz, toKhz));
}

static bool isFm(uint32_t khz)
{
  return(bandFor(FM, khz, khz) >= 0);
}

// Index into the FM bandwidth menu: Auto, 110k, 84k, 60k, 40k
static uint8_t fmFilterIndex(uint32_t hz)
{
  return(hz == 0 ? 0 : hz >= 100000 ? 1 : hz >= 80000 ? 2 : hz >= 60000 ? 3 : 4);
}

// Exact AM widths only, anything else is 2 kHz as in FM-DX Tuner
static uint8_t amWidthIndex(uint32_t hz)
{
  for(uint8_t i = 0; i < ITEM_COUNT(amWidths); i++)
    if(amWidths[i].hz == hz) return(i);
  return(2);
}

// Exact SSB widths only, anything else is 2.2 kHz
static uint8_t ssbWidthIndex(uint32_t hz)
{
  for(uint8_t i = 0; i < ITEM_COUNT(ssbWidths); i++)
    if(ssbWidths[i].hz == hz) return(i);
  return(3);
}

// 0 = correct, 1 = very likely, 2 = likely, 3 = unlikely, 4 = invalid
static uint8_t piAdd(uint16_t pi, bool error)
{
  piPos = (piPos + 1) % 64;
  piHistory[piPos] = pi;
  if(error) piErrors |= 1ULL << piPos; else piErrors &= ~(1ULL << piPos);
  if(piFill < 64) piFill++;

  uint8_t count = 0, correct = 0;
  for(uint8_t i = 0; i < piFill; i++)
  {
    if(piHistory[i] != pi) continue;
    count++;
    if(!((piErrors >> i) & 1)) correct++;
  }

  if(correct >= 2) return(0);
  if(count >= 2 && correct) return(1);
  if(count >= 3) return(2);
  if(count == 2 || correct) return(3);
  return(4);
}

static void rdsClear()
{
  piFill = 0;
  piPos = 63;
  // Drop groups still queued from the previous station
  if(currentMode == FM) rx.getRdsStatus(0, 1, 0);
}

static bool waitCts()
{
  const uint8_t addr = rx.getDeviceAddress();
  for(uint32_t start = millis(); millis() - start < FMDX_CTS_TIMEOUT; delayMicroseconds(200))
    if(Wire.requestFrom(addr, (uint8_t)1, (uint8_t)true) == 1 && (Wire.read() & 0x80)) return(true);
  return(false);
}

static bool sendCommand(const uint8_t *data, size_t len)
{
  if(!waitCts()) return(false);
  Wire.beginTransmission((uint8_t)rx.getDeviceAddress());
  Wire.write(data, len);
  return(Wire.endTransmission() == 0);
}

static bool query(uint8_t cmd, uint8_t arg, uint8_t *resp, uint8_t len)
{
  const uint8_t data[] = { cmd, arg };
  if(!sendCommand(data, sizeof(data)) || !waitCts()) return(false);
  if(Wire.requestFrom((uint8_t)rx.getDeviceAddress(), len, (uint8_t)true) != len) return(false);
  for(uint8_t i = 0; i < len; i++) resp[i] = Wire.read();
  return(true);
}

// Tune to one scan point and return its RSSI, or -1 on failure.
// AM with no antenna capacitor given tunes it automatically and returns the value found.
static int scanPoint(bool am, uint32_t khz, bool fast, uint16_t &antcap)
{
  const uint16_t freq = am ? khz : khz / 10;
  const uint8_t tune[] =
  {
    am ? CMD_AM_TUNE_FREQ : CMD_FM_TUNE_FREQ, (uint8_t)(fast ? 0x01 : 0x00),
    (uint8_t)(freq >> 8), (uint8_t)freq, (uint8_t)(antcap >> 8), (uint8_t)antcap
  };
  const uint8_t status = am ? CMD_AM_TUNE_STATUS : CMD_FM_TUNE_STATUS;
  uint8_t resp[8];

  if(!sendCommand(tune, am ? 6 : 5)) return(-1);
  const uint32_t tunedAt = millis();

  // A fast tune's status is inaccurate, so only its completion is used
  while(!query(status, 0x00, resp, 8) || !(resp[0] & 0x01))
  {
    if(millis() - tunedAt >= FMDX_STC_TIMEOUT) return(-1);
    delay(1);
  }
  if(am && !antcap) antcap = (resp[6] << 8) | resp[7];
  query(status, 0x01, resp, 8);

  while(millis() - tunedAt < FMDX_SCAN_SETTLE) delay(1);
  return(query(am ? CMD_AM_RSQ_STATUS : CMD_FM_RSQ_STATUS, 0x00, resp, am ? 6 : 8) ? resp[4] : -1);
}

static void reportMode()
{
  Serial.printf("M%u\n", (unsigned)protocolMode(currentMode));
}

static void reportTune()
{
  reportedHz = currentFrequency;
  reportedMode = currentMode;

  // SSB tunes finer than 1 kHz, which is sent as decimal kHz
  const unsigned khz = currentFrequency / 1000;
  const unsigned rest = currentFrequency % 1000 / 10;
  if(rest) Serial.printf("T%u.%02u,1\n", khz, rest);
  else Serial.printf("T%u,%u\n", khz, currentMode == FM ? 10U : 1U);
}

static void reportQuality()
{
  rx.getCurrentReceivedSignalQuality();
  const bool pilot = currentMode == FM && rx.getCurrentPilot();
  // dBuV to dBf, as FM-DX Tuner reports it
  Serial.printf("S%c%d.25,0,0,-1\n",
    stereoOutput ? (pilot ? 's' : 'm') : (pilot ? 'S' : 'M'), rx.getCurrentRSSI() + 11);
}

static bool pollRds()
{
  bool needRedraw = false;

  // Count the queued groups first, so reading never runs past the end of the FIFO
  rx.getRdsStatus(0, 0, 1);
  for(uint8_t groups = rx.getNumRdsFifoUsed(); groups; groups--)
  {
    rx.getRdsStatus(0, 0, 0);
    const auto &rds = rx.getRdsStatusRaw().resp;
    const uint16_t pi = (rds.BLOCKAH << 8) | rds.BLOCKAL;
    const uint8_t piState = piAdd(pi, rds.BLEA != 0);

    if(piState < 4) Serial.printf("P%04X%.*s\n", (unsigned)pi, piState, "???");
    // Legacy group message: blocks B to D, then their error levels
    Serial.printf("R%04X%04X%04X%02X\n",
      (unsigned)((rds.BLOCKBH << 8) | rds.BLOCKBL),
      (unsigned)((rds.BLOCKCH << 8) | rds.BLOCKCL),
      (unsigned)((rds.BLOCKDH << 8) | rds.BLOCKDL),
      (unsigned)(rds.BLEB | (rds.BLEC << 2) | (rds.BLED << 4)));

    if(snr >= 12) needRedraw |= decodeRds();
  }

  return(needRedraw);
}

static int totalSavedBands()
{
  return(min(getTotalBands(), (int)ITEM_COUNT(saved.bandwidth)));
}

// Switch the band to the mode as the Mode menu does, then select it if anything changed
static void selectBandMode(int band, uint8_t mode)
{
  const bool converted = bands[band].bandMode != mode;
  if(converted)
  {
    // As doMode(), with the default step and bandwidth for the new mode
    bands[band].bandMode = mode;
    bands[band].currentStepIdx = mode == AM ? 1 : 5;
    bands[band].bandwidthIdx = 4;
    if(band < totalSavedBands())
    {
      applied.mode[band] = mode;
      applied.step[band] = bands[band].currentStepIdx;
      applied.bandwidth[band] = bands[band].bandwidthIdx;
    }
  }
  if(band != bandIdx || converted) selectBand(band, false);
}

static bool startSession()
{
  saved.volume = volume;
  saved.region = FmRegionIdx;
  saved.stereo = fmStereoIdx;
  saved.squelch = currentSquelch[FM];
  saved.fmAgc = FmAgcIdx;
  saved.amAgc = AmAgcIdx;
  saved.ssbAgc = SsbAgcIdx;
  for(int i = 0; i < totalSavedBands(); i++)
  {
    saved.mode[i] = bands[i].bandMode;
    saved.step[i] = bands[i].currentStepIdx;
    saved.bandwidth[i] = bands[i].bandwidthIdx;
  }
  saved.muted = muteOn(MUTE_MAIN);
  applied = saved;

  active = true;
  stereoOutput = fmStereoIdx == FM_STEREO_AUTO;
  qualityInterval = FMDX_QUALITY_INTERVAL;
  alignment = 0;
  reportedHz = currentFrequency;
  reportedMode = currentMode;
  stalled = false;
  rdsClear();
  statusShow("Webserver connected");
  return(true);
}

static bool endSession(const char *message)
{
  if(!active) return(false);
  active = false;

  bool restored = false;
  auto revert = [&](auto &value, auto webserver, auto original)
  {
    if(value != webserver || webserver == original) return;
    value = original;
    restored = true;
  };

  revert(volume, applied.volume, saved.volume);
  revert(FmRegionIdx, applied.region, saved.region);
  revert(fmStereoIdx, applied.stereo, saved.stereo);
  revert(currentSquelch[FM], applied.squelch, saved.squelch);
  revert(FmAgcIdx, applied.fmAgc, saved.fmAgc);
  revert(AmAgcIdx, applied.amAgc, saved.amAgc);
  revert(SsbAgcIdx, applied.ssbAgc, saved.ssbAgc);
  for(int i = 0; i < totalSavedBands(); i++)
  {
    revert(bands[i].bandMode, applied.mode[i], saved.mode[i]);
    revert(bands[i].currentStepIdx, applied.step[i], saved.step[i]);
    revert(bands[i].bandwidthIdx, applied.bandwidth[i], saved.bandwidth[i]);
  }

  rx.setVolume(volume);
  // A mode put back on the current band only takes effect by selecting the band again
  if(bands[bandIdx].bandMode != currentMode)
    selectBand(bandIdx, false);
  else
  {
    if(currentMode == FM)
    {
      rx.setFMDeEmphasis(fmRegions[FmRegionIdx].value);
      applyFmStereo();
    }
    doAgc(0);
    doBandwidth(0);
  }
  if(muteOn(MUTE_MAIN) == applied.muted && applied.muted != saved.muted)
    muteOn(MUTE_MAIN, saved.muted);

  // A local change may have saved the webserver's values along with it
  if(restored) prefsRequestSave(SAVE_SETTINGS | SAVE_BANDS);

  if(message) statusShow(message);
  return(true);
}

static bool cmdTune(const char *args)
{
  // Decimal kHz, so SSB can tune finer than 1 kHz
  const int64_t hz = llround(strtod(args, nullptr) * 1000);
  if(hz <= 0 || hz > UINT32_MAX) return(false);
  const uint32_t khz = hz / 1000;

  // HF frequencies keep the current HF mode, starting in AM from FM
  const uint8_t mode = isFm(khz) ? FM : currentMode == FM ? AM : currentMode;
  const int band = mode == FM ? bandFor(FM, khz, khz) : hfBandFor(mode, khz, khz);
  if(band < 0) return(false);

  const uint8_t prevMode = currentMode;
  const uint32_t prevHz = currentFrequency;
  selectBandMode(band, mode);
  updateFrequency(hz, false);

  // Fine tuning around the same station keeps its station information
  const uint32_t moved = currentFrequency > prevHz ? currentFrequency - prevHz : prevHz - currentFrequency;
  if(currentMode != prevMode || moved > (currentMode == FM ? 10000U : 1000U))
  {
    clearStationInfo();
    identifyFrequency(currentFrequency);
    rdsClear();
  }

  if(currentMode != prevMode) reportMode();
  reportTune();
  Serial.printf("V%u\n", (unsigned)alignment);
  return(true);
}

static bool cmdMode(uint32_t value)
{
  if(value >= ITEM_COUNT(protocolModes)) return(false);
  const uint8_t mode = protocolModes[value];

  // HF modes switch the current HF band, as the Mode menu does
  int band = mode == FM ? widestBand(FM) : currentMode != FM ? bandIdx : widestBand(mode);
  if(band < 0 && mode != FM) band = widestBand(mode, true);
  if(band < 0) return(false);

  const uint8_t prevMode = currentMode;
  const uint32_t prevHz = currentFrequency;
  selectBandMode(band, mode);

  rdsClear();
  Serial.printf("M%u\n", (unsigned)value);
  if(currentMode != prevMode || currentFrequency != prevHz) reportTune();
  return(currentMode != prevMode);
}

static void setBandwidthIdx(int8_t idx)
{
  getCurrentBand()->bandwidthIdx = idx;
  if(bandIdx < totalSavedBands()) applied.bandwidth[bandIdx] = idx;
  doBandwidth(0);
}

static bool cmdBandwidth(uint32_t hz)
{
  static const uint32_t fmWidths[] = { 0, 110000, 84000, 60000, 40000 };

  if(currentMode == FM)
  {
    const uint8_t idx = fmFilterIndex(hz);
    setBandwidthIdx(idx);
    Serial.printf("W%u\n", (unsigned)fmWidths[idx]);
    return(true);
  }

  if(currentMode == AM)
  {
    const uint8_t idx = amWidthIndex(hz);
    setBandwidthIdx(amWidths[idx].menu);
    Serial.printf("W%u\n", (unsigned)amWidths[idx].hz);
    return(true);
  }

  const uint8_t idx = ssbWidthIndex(hz);
  setBandwidthIdx(ssbWidths[idx].menu);
  Serial.printf("W%u\n", (unsigned)ssbWidths[idx].hz);
  return(true);
}

static bool cmdVolume(uint32_t value)
{
  if(value > 100) return(false);

  applied.volume = volume = (uint8_t)map(value, 0, 100, 0, 63);
  rx.setVolume(volume);
  if(muteOn(MUTE_MAIN)) muteOn(MUTE_MAIN, false);
  applied.muted = false;
  Serial.printf("Y%u\n", (unsigned)value);
  return(true);
}

static bool cmdDeemphasis(uint32_t value)
{
  // 0 = 50 us, 1 = 75 us, matching the FM Region order; the receiver cannot turn it off (2)
  if(value > 1) return(false);

  applied.region = FmRegionIdx = value;
  if(currentMode == FM) rx.setFMDeEmphasis(fmRegions[FmRegionIdx].value);
  Serial.printf("D%u\n", (unsigned)value);
  return(false);
}

static bool cmdAgc(uint32_t value)
{
  // Webserver gain 0 = auto, 1 = high, 3 = medium, 2 = low.
  // The receiver uses 0 = AGC, n = attenuation n - 1, up to 26 on FM and 36 on AM,
  // while SSB only has AGC on or off.
  static const int8_t fmLevels[] = { 0, 1, 27, 14 };
  static const int8_t amLevels[] = { 0, 1, 37, 19 };
  if(value > 3) return(false);

  applied.fmAgc = FmAgcIdx = fmLevels[value];
  applied.amAgc = AmAgcIdx = amLevels[value];
  applied.ssbAgc = SsbAgcIdx = value ? 1 : 0;
  doAgc(0);
  Serial.printf("A%u\n", (unsigned)value);
  return(true);
}

static bool cmdOutputMode(uint32_t value)
{
  // 0 = stereo, 1 = mono; MPX output (2) is not available
  if(value > 1) return(false);

  applied.stereo = fmStereoIdx = value ? FM_STEREO_MONO : FM_STEREO_AUTO;
  stereoOutput = !value;
  applyFmStereo();
  Serial.printf("B%u\n", (unsigned)value);
  return(true);
}

static bool cmdSquelch(int32_t value)
{
  // The webserver's level is in dBf, the receiver's in dBuV; stereo squelch (negative) is not available
  applied.squelch = currentSquelch[FM] = value > 0 ? constrain(value - 11, 0, 127) : 0;
  Serial.printf("Q%d\n", (int)value);
  return(false);
}

static void runScan(bool repeat)
{
  if(!scanStep || !scanFrom || scanFrom > scanTo) return;

  const uint8_t mode = isFm(scanFrom) ? FM : AM;
  int band = mode == FM ? bandFor(FM, scanFrom, scanTo) : hfBandFor(AM, scanFrom, scanTo);
  if(band < 0) band = widestBand(mode, mode != FM);
  if(band < 0) return;

  // Keep to the points the band can tune, on the requested step grid
  uint32_t from = scanFrom;
  const uint32_t to = min(scanTo, bandMaxKhz(band));
  if(from < bandMinKhz(band)) from += (bandMinKhz(band) - from + scanStep - 1) / scanStep * scanStep;
  if(from > to) return;

  const bool am = mode == AM;
  const int prevBand = bandIdx;
  const uint32_t prevFreq = currentFrequency;
  const uint8_t bandMode = bands[band].bandMode;
  uint8_t resp[8];

  // Each scan point is dozens of I2C transactions, whose overhead is CPU bound
  const uint32_t cpuMhz = getCpuFrequencyMhz();
  setCpuFrequencyMhz(240);

  // Scans read the signal in AM, so an SSB band is switched to AM until the scan ends
  bands[band].bandMode = mode;
  if(band != bandIdx || bandMode != mode) selectBand(band, false);
  rx.setAudioMute(true);
  // Seek validity is unused, an unreachable threshold shortens tunes on occupied channels
  if(am)
  {
    rx.setBandwidth(amWidths[amWidthIndex(scanBandwidth)].filter, 1);
    rx.setSeekAmRssiThreshold(63);
  }
  else
  {
    rx.setFmBandwidth(fmFilterIndex(scanBandwidth));
    rx.setSeekFmRssiThreshold(127);
  }
  // Acknowledge any earlier tune, so the first point waits for its own
  query(am ? CMD_AM_TUNE_STATUS : CMD_FM_TUNE_STATUS, 0x01, resp, 8);

  // AM finds the antenna capacitor on the first point, then reuses it with fast tunes
  uint16_t antcap = 0;
  bool stop = false;
  do
  {
    Serial.print('U');
    for(uint32_t khz = from; ; )
    {
      const int rssi = scanPoint(am, khz, !am || antcap, antcap);
      if(rssi < 0)
      {
        stop = true;
        break;
      }
      Serial.printf("%u=%d.25", (unsigned)(am ? khz : khz / 10 * 10), rssi + 11);

      khz += scanStep;
      if(khz > to) break;
      Serial.print(',');

      // Any new command cancels the scan, leaving the trailing comma that marks it incomplete
      if(Serial.available())
      {
        stop = true;
        break;
      }
    }
    Serial.print('\n');
  }
  while(repeat && !stop && !Serial.available());

  // Restore the seek thresholds set by useBand()
  if(am) rx.setSeekAmRssiThreshold(10); else rx.setSeekFmRssiThreshold(5);
  bands[band].bandMode = bandMode;
  if(bandIdx != prevBand || currentMode != bands[prevBand].bandMode)
    selectBand(prevBand, false);
  else
    doBandwidth(0);
  updateFrequency(prevFreq, false);
  rdsClear();
  if(!muteOn(MUTE_MAIN) && !muteOn(MUTE_SQUELCH)) rx.setAudioMute(false);
  setCpuFrequencyMhz(cpuMhz);
}

static bool cmdScan(const char *args)
{
  switch(args[0])
  {
    case 'a': scanFrom = atol(args + 1); break;
    case 'b': scanTo = atol(args + 1); break;
    case 'c': scanStep = atol(args + 1); break;
    case 'w': scanBandwidth = atol(args + 1); break;
    case 'm':
    case '\0':
      runScan(args[0] == 'm');
      return(true);
  }
  return(false);
}

static bool processCommand(const char *cmd)
{
  const char *args = cmd[0] ? cmd + 1 : cmd;
  const uint32_t value = atol(args);

  if(cmd[0] == 'x')
  {
    Serial.print("\nOK\n");
    return(!active && startSession());
  }

  // Everything else waits for the webserver to start a session
  if(!active) return(false);

  switch(cmd[0])
  {
    case 'X': return(endSession("Webserver disconnected"));
    case 'T': return(cmdTune(args));
    case 'M': return(cmdMode(value));
    case 'W': return(cmdBandwidth(value));
    case 'Y': return(cmdVolume(value));
    case 'D': return(cmdDeemphasis(value));
    case 'A': return(cmdAgc(value));
    case 'B': return(cmdOutputMode(value));
    case 'Q': return(cmdSquelch(atol(args)));
    case 'S': return(cmdScan(args));
    case 'I':
      if(value > 1000) return(false);
      qualityInterval = value;
      Serial.printf("I%u\n", (unsigned)value);
      return(false);
    case 'V':
      alignment = value;
      Serial.printf("V%u\n", (unsigned)value);
      return(false);
    case 'G':
      Serial.printf("G%s\n", args);
      return(false);
  }

  return(false);
}

bool fmdxLoop()
{
  bool needRedraw = false;

  // HWCDC can briefly report a false disconnect, so only a sustained one ends the session
  if(!Serial && !Serial.available())
  {
    if(!disconnectPending)
    {
      disconnectPending = true;
      disconnectedAt = millis();
    }
    else if(millis() - disconnectedAt >= FMDX_DISCONNECT_TIME)
      needRedraw |= endSession("Webserver disconnected");
    return(needRedraw);
  }
  disconnectPending = false;

  for(int c; (c = Serial.read()) >= 0; )
  {
    if(c == '\r') continue;
    if(c != '\n')
    {
      if(cmdLength < sizeof(cmdLine) - 1) cmdLine[cmdLength++] = c;
      continue;
    }
    cmdLine[cmdLength] = '\0';
    cmdLength = 0;
    needRedraw |= processCommand(cmdLine);
  }

  if(!active) return(needRedraw);

  const uint32_t now = millis();

  // A host that stopped reading has gone away, so hand the receiver back
  if(Serial.availableForWrite() < FMDX_STALL_FREE)
  {
    if(!stalled)
    {
      stalled = true;
      stalledAt = now;
    }
    else if(now - stalledAt >= FMDX_STALL_TIME)
      needRedraw |= endSession("Webserver disconnected");
    return(needRedraw);
  }
  stalled = false;

  // Keep the webserver in step with tuning from other controls
  if(currentMode != reportedMode) reportMode();
  if(currentMode != reportedMode || currentFrequency != reportedHz) reportTune();

  if(qualityInterval && now - lastQuality >= qualityInterval)
  {
    lastQuality = now;
    reportQuality();
  }

  if(currentMode == FM && now - lastRds >= FMDX_RDS_INTERVAL)
  {
    lastRds = now;
    needRedraw |= pollRds();
  }

  return(needRedraw);
}

bool fmdxActive()
{
  return(active);
}

void fmdxReset()
{
  endSession(nullptr);
  cmdLength = 0;
  disconnectPending = false;
}

bool fmdxAbortPending()
{
  return(active && Serial.available() > 0);
}
