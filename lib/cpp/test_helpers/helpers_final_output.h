#pragma once

#include <algorithm>
#include <cstddef>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

inline std::vector<std::string> SortedOutput(const std::string& src,
                                             SimFixture& f) {
  std::string out = RunCapture(src, f);
  std::ostringstream finals;
  std::streambuf* old_buf = std::cout.rdbuf(finals.rdbuf());
  f.ctx.RunFinalBlocks();
  std::cout.rdbuf(old_buf);
  out += finals.str();
  std::vector<std::string> lines;
  size_t start = 0;
  while (start < out.size()) {
    size_t end = out.find('\n', start);
    if (end == std::string::npos) end = out.size();
    std::string line = out.substr(start, end - start);
    if (!line.empty() && !line.starts_with("$finish")) lines.push_back(line);
    start = end + 1;
  }
  std::sort(lines.begin(), lines.end());
  return lines;
}

inline std::vector<std::string> SortedOutput(const std::string& src) {
  SimFixture f;
  return SortedOutput(src, f);
}
