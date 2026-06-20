#pragma once

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Performs the standard VCD dump setup shared by the §21.7 system-task tests:
// creates the canonical "clk" (1-bit, value 1) and "data" (8-bit, value 0xA5)
// variables, registers them with the writer, finishes the definition section,
// writes the initial timestamp and installs the writer on the simulation
// context so a subsequent $dump* system call observes it. The caller owns the
// VcdWriter (so its destructor flushes into the test's scope before ReadVcd).
inline void SetupClkDataDump(SimFixture& f, VcdWriter& vcd) {
  auto* clk = MakeVar(f, "clk", 1, 1);
  auto* data = MakeVar(f, "data", 8, 0xA5);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("clk", 1, clk);    // ident '!'
  vcd.RegisterSignal("data", 8, data);  // ident '"'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);
}

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
