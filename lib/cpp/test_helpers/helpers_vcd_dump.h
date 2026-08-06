#pragma once

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Counts the number of (non-overlapping) occurrences of `sub` in `s`. Used by
// the §21.7 dump tests to assert how many checkpoint markers were emitted.
inline std::size_t CountOccurrences(const std::string& s,
                                    const std::string& sub) {
  std::size_t n = 0;
  for (std::size_t pos = s.find(sub); pos != std::string::npos;
       pos = s.find(sub, pos + sub.size())) {
    ++n;
  }
  return n;
}
