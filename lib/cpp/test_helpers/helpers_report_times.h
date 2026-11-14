#pragma once

#include <cstddef>
#include <string>

inline std::string ReportTimes(const std::string& out,
                               const std::string& label) {
  std::string times;
  std::string head = label + " at ";
  size_t start = 0;
  while (start < out.size()) {
    size_t end = out.find('\n', start);
    if (end == std::string::npos) end = out.size();
    if (out.compare(start, head.size(), head) == 0) {
      if (!times.empty()) times += ' ';
      times.append(out, start + head.size(), end - start - head.size());
    }
    start = end + 1;
  }
  return times;
}
