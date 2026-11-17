#pragma once

#include <cstddef>
#include <cstdio>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

inline std::string PlaceholderPath(const std::string& family,
                                   const std::string& tag, int index) {
  return "/tmp/deltahdl_" + family + "_" + tag + "_" + std::to_string(index);
}

inline std::string RunWithPlaceholderPaths(const std::string& family,
                                           const std::string& tag,
                                           std::string src, SimFixture& f) {
  for (int i = 0; i < 4; ++i) {
    const std::string kToken = "<P" + std::to_string(i) + ">";
    for (size_t at = src.find(kToken); at != std::string::npos;
         at = src.find(kToken)) {
      src.replace(at, kToken.size(), PlaceholderPath(family, tag, i));
    }
  }
  return RunCapture(src, f);
}

inline void RemovePlaceholderPaths(const std::string& family,
                                   const std::string& tag) {
  for (int i = 0; i < 4; ++i) {
    std::remove(PlaceholderPath(family, tag, i).c_str());
  }
}
