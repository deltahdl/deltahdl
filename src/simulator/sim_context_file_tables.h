#pragma once

// The tables SimContext keeps of the files a design opens and reads through
// the §21.3 file I/O tasks: the descriptors open, which of them may be read,
// the last error of each, the end-of-file a scan detected, the characters
// pushed back onto a descriptor no host stream reads, the $fmonitor tasks set
// up, and the files of the multichannel descriptor's channels. The operations
// on them are SimContext's own, in src/simulator/sim_context_fileio.cpp.

#include <array>
#include <cstddef>
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
  SimFileTables() = default;
  SimFileTables(const SimFileTables&) = delete;
  SimFileTables& operator=(const SimFileTables&) = delete;
  // A file the design or an application opened and nothing closed is closed
  // with the run, its text written out; the standard streams are left open.
  ~SimFileTables() {
    for (auto& [descriptor, file] : descriptors) {
      if (file != stdin && file != stdout && file != stderr) std::fclose(file);
    }
    for (std::size_t bit = 1; bit < mcd_channels.size(); ++bit) {
      if (mcd_channels[bit] != nullptr) std::fclose(mcd_channels[bit]);
    }
  }

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
  // §38.26: the name each open file was opened under, keyed by its fd, or by
  // the one channel bit of its multichannel descriptor.
  std::unordered_map<uint32_t, std::string> names;
  bool stdio_ready = false;
};

}  // namespace delta
