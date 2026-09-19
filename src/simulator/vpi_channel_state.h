#pragma once

#include <string>
#include <unordered_map>

#include "simulator/vpi_user.h"

namespace delta {

// §38.5, §38.25 to §38.28: the text the tool's output channel, its log file and
// each open multichannel descriptor hold, the descriptors vpi_mcd_open() has
// handed out, and the test hooks that drive the routines over them down their
// failure returns. VpiContext owns one of these and its channel routines read
// and write it; it stands apart from the context so that the state the four
// clauses describe is declared in one place.
struct VpiChannelState {
  // §38.5: the simulator's output channel and current log file each hold
  // written text in an in-memory buffer until vpi_flush() commits it. A flush
  // appends each buffer to its committed stream and clears the buffer.
  std::string output_channel_buffer;
  std::string output_channel_flushed;
  std::string log_file_buffer;
  std::string log_file_flushed;
  // Test hook that drives vpi_flush() down its failure return.
  bool flush_should_fail = false;

  // §38.27: descriptors handed out by vpi_mcd_open(), keyed by file name so a
  // repeated open of the same file returns the descriptor it already holds.
  // mcd_allocated_channels marks every channel bit currently in use - both the
  // ones this routine assigned and any seeded from $fopen - so a fresh open can
  // pick an unused channel. Channel 1 (LSB) and channel 32 (MSB) are reserved
  // and never selected.
  std::unordered_map<std::string, PLI_UINT32> mcd_open_files;
  PLI_UINT32 mcd_allocated_channels = 0;
  // Test hook that drives vpi_mcd_open() down its error return.
  bool mcd_open_should_fail = false;

  // §38.25: each open mcd channel holds the text written to its file in an
  // in-memory buffer until vpi_mcd_flush() commits it. A flush appends each
  // named channel's buffer to its committed stream and clears the buffer. Keyed
  // by the single channel bit so one descriptor's several channels are flushed
  // together.
  std::unordered_map<PLI_UINT32, std::string> mcd_channel_buffers;
  std::unordered_map<PLI_UINT32, std::string> mcd_channel_flushed;
  // Test hook that drives vpi_mcd_flush() down its failure return.
  bool mcd_flush_should_fail = false;
  // Returned by the channel accessors when a channel has no buffered or flushed
  // text, so they can hand back a reference without inserting an entry. Nothing
  // writes to it; it is not declared const because a const data member would
  // fall under readability-identifier-naming's constant rule and need a k
  // prefix, which no other member of this struct carries.
  std::string empty_mcd_buffer;

  // §38.26: the single buffer vpi_mcd_name() reuses for its result, so each
  // call overwrites the previous returned value. Separate from get_str_buffer_.
  std::string mcd_name_buffer;
};

}  // namespace delta
