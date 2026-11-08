#pragma once

#include <string>
#include <vector>

namespace delta {

struct ArgOrigins {
  std::string path;
  std::vector<int> lines;
};

inline std::string ArgOriginPrefix(const ArgOrigins* origins, int i) {
  if (origins == nullptr) return "";
  return origins->path + ":" + std::to_string(origins->lines[i]) + ": ";
}

}  // namespace delta
