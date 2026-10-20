#pragma once

#include <string>
#include <string_view>

#include "simulator/vpi_user.h"

namespace delta {

class SimContext;

// §38.24 to §38.28 with §21.3.1: in a run, the descriptors vpi_mcd_open()
// hands out and those $fopen returns are one namespace, the run's file table,
// which the VPI routines and the built-in file tasks write through alike.

// §38.27: the multichannel descriptor of `name`, the one already open on it
// as a multichannel descriptor or a channel newly opened for writing; 0 where
// none can be opened.
PLI_UINT32 VpiRunMcdOpen(SimContext& run, const std::string& name);

// §38.24: close the file of the fd `mcd`, or of each channel the
// multichannel descriptor `mcd` selects; 0 when all were closed, else what was
// left open: the fd itself, or the channels, channel 1 among them.
PLI_UINT32 VpiRunMcdClose(SimContext& run, PLI_UINT32 mcd);

// §38.26: the name the file of the fd or single channel `cd` was opened
// under, null where it names no open file.
const std::string* VpiRunFileName(SimContext& run, PLI_UINT32 cd);

// §38.28: write `text` to the file of the one channel `channel`, past
// channel 1, where one is open.
void VpiRunMcdWrite(SimContext& run, PLI_UINT32 channel, std::string_view text);

// §38.25: flush the file of the one channel `channel`, past channel 1; false
// where the flush failed.
bool VpiRunMcdFlush(SimContext& run, PLI_UINT32 channel);

}  // namespace delta
