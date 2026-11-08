#pragma once

#include <cstddef>
#include <string>

inline std::size_t CountOccurrences(const std::string& s,
                                    const std::string& sub) {
  std::size_t n = 0;
  for (std::size_t pos = s.find(sub); pos != std::string::npos;
       pos = s.find(sub, pos + sub.size())) {
    ++n;
  }
  return n;
}
