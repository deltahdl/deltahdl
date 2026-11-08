#pragma once

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
  ~SimFileTables() {
    for (auto& [descriptor, file] : descriptors) {
      if (file != stdin && file != stdout && file != stderr) std::fclose(file);
    }
    for (std::size_t bit = 1; bit < mcd_channels.size(); ++bit) {
      if (mcd_channels[bit] != nullptr) std::fclose(mcd_channels[bit]);
    }
  }

  std::unordered_map<uint32_t, FILE*> descriptors;
  std::unordered_set<uint32_t> readable;
  std::unordered_map<uint32_t, FileIoError> errors;
  std::unordered_set<uint32_t> eof_detected;
  std::unordered_map<uint32_t, std::string> pushback;
  std::vector<std::unique_ptr<FileMonitor>> monitors;
  std::array<FILE*, 31> mcd_channels = {};
  std::unordered_map<uint32_t, std::string> names;
  bool stdio_ready = false;
};

}  // namespace delta
