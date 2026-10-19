#pragma once

// The tables SimContext keeps of the files a design opens and reads through
// the §21.3 file I/O tasks: the descriptors open, which of them may be read,
// the last error of each, the end-of-file a scan detected, the characters
// pushed back onto a descriptor no host stream reads, the $fmonitor tasks set
// up, and the files of the multichannel descriptor's channels. The operations
// on them are SimContext's own, in src/simulator/sim_context_fileio.cpp.

#include <array>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/file_monitor.h"
#include "simulator/sim_context_types.h"

namespace delta {

struct SimFileTables {
  std::unordered_map<uint32_t, FILE*> descriptors;
  // §21.3.4: descriptors whose open type permits reading ("r"/"r+" families).
  std::unordered_set<uint32_t> readable;
  // §21.3.7: most-recent-operation error per descriptor, keyed by the fd value
  // as the operation received it -- so a failure on an invalid descriptor is
  // still queryable through $ferror with that same value.
  std::unordered_map<uint32_t, FileIoError> errors;
  std::unordered_set<uint32_t> eof_detected;
  std::unordered_map<uint32_t, std::string> pushback;
  std::vector<std::unique_ptr<FileMonitor>> monitors;
  // Bit i in mcd_channels[i] tracks the file opened on channel i (1..30).
  std::array<FILE*, 31> mcd_channels = {};
  bool stdio_ready = false;
};

}  // namespace delta
