#ifndef FMDX_MODE_H
#define FMDX_MODE_H

#include <Arduino.h>

// FM-DX Webserver tuner protocol over the USB serial port.
// Return whether the display needs updating.
bool fmdxLoop();
// The webserver has started a session
bool fmdxActive();
// End the session when the USB port leaves Webserver mode
void fmdxReset();
// Pending webserver input should cancel a blocking operation
bool fmdxAbortPending();

#endif
