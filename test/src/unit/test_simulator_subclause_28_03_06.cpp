#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §28.3.6: when a terminal's width equals the instance-array length it is
// distributed — each element connects to its own bit of the terminal. A row of
// four `and` gates over 4-bit terminals therefore computes the bitwise AND, one
// bit per element, rather than any whole-word reduction.
TEST(GateArrayRuntime, NInputArrayDistributesPerBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  wire [3:0] y;\n"
      "  initial begin a = 4'b1100; b = 4'b1010; end\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  // 1100 & 1010 == 1000
  EXPECT_EQ(w.aval & 0xFu, 0x8u);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

// §28.3.6: a single-bit terminal is broadcast to every element of the array.
// This is the LRM's own three-state array example — a scalar enable feeding a
// row of buffers whose data and outputs are distributed. With the enable
// asserted for conduction, every element passes its own data bit, so the output
// word equals the input word.
TEST(GateArrayRuntime, ScalarEnableBroadcastsAcrossThreeStateArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] in;\n"
      "  logic en;\n"
      "  wire [3:0] out;\n"
      "  initial begin in = 4'b1011; en = 1'b0; end\n"
      "  bufif0 ar[3:0](out, in, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("out");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  // en == 0 conducts on every element, so out == in == 1011.
  EXPECT_EQ(w.aval & 0xFu, 0xBu);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

// §28.3.6: a distributed control terminal is likewise part-selected per element
// — each buffer sees only its own enable bit, not a word-wide reduction of the
// whole control vector. With enable 1010 a bufif0 row conducts on the bits
// whose enable is 0 (bits 0 and 2), so those output bits follow their data
// while the disabled bits are not driven to a logic 1. The word-reduced
// (pre-fix) result would have turned the entire array off.
TEST(GateArrayRuntime, DistributedEnableAppliesPerElementControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] in, en;\n"
      "  wire [3:0] out;\n"
      "  initial begin in = 4'b1111; en = 4'b1010; end\n"
      "  bufif0 ar[3:0](out, in, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("out");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  // Conducting bits (enable 0) are bits 0 and 2, each passing its data bit 1.
  EXPECT_EQ(w.aval & 0xFu, 0x5u);
}

}  // namespace
