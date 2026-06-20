#pragma once

#include <string>

#include "fixture_simulator.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Builds the shared "buffered dump" scenario used by the $dumpflush /
// $dumpportsflush flush tests: registers a 1-bit clk (ident '!') and an 8-bit
// data (ident '"') signal on the supplied writer, opens the value-change
// section at time 0, and dumps all values so the records sit in the writer's
// buffer (not yet on disk). Returns the data variable for follow-on assertions.
//
// The writer is constructed by the caller (so it can outlive this helper and be
// flushed afterwards). `buffered_content` is the current file contents, which
// the caller obtains from its fixture's ReadVcd(); this helper asserts that the
// freshly buffered data record is not yet present in the file.
inline Variable* SetupBufferedVcdDump(SimFixture& f, VcdWriter& vcd,
                                      const std::string& buffered_content) {
  auto* clk = MakeVar(f, "clk", 1, 1);
  auto* data = MakeVar(f, "data", 8, 0xA5);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("clk", 1, clk);    // ident '!'
  vcd.RegisterSignal("data", 8, data);  // ident '"'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  vcd.DumpAllValues();

  // Nothing flushed yet: the value records are still buffered.
  EXPECT_EQ(buffered_content.find("b10100101 \""), std::string::npos);

  f.ctx.SetVcdWriter(&vcd);
  return data;
}
