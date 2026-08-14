#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SynthLower, AssignTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b, output y);\n"
                           "  assign y = sel ? a : b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, NestedTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input s1, input s0, input a, input b,\n"
                           "         input c, output y);\n"
                           "  assign y = s1 ? (s0 ? a : b) : c;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 5);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, TernaryMuxWideBus) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input sel, input [7:0] a, input [7:0] b, output [7:0] y);\n"
      "  assign y = sel ? a : b;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8);
}

TEST(SynthLower, ChainedTernaryPriorityMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input [1:0] sel, input a, input b, input c, output y);\n"
      "  assign y = (sel == 2'd0) ? a : (sel == 2'd1) ? b : c;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  // The sweep fails on the netlist this module lowered to before `sel == 2'd0`
  // and `sel == 2'd1` had a lowering: both comparisons answered
  // `AigGraph::kConstFalse`, and `AigGraph::AddMux` with a constant-false
  // select hands back the else literal and builds no node, so `y` carried `c`
  // for every value of `sel` and `a` and `b` reached nothing. The output count
  // above never noticed, because the port list fixes that count whatever the
  // netlist computes.
  //
  // `SynthLower::MapPorts` walks `mod->ports` in declaration order and
  // allocates one AIG input per bit, low bit first, so bit 0 of the word is
  // sel[0], bit 1 is sel[1], bit 2 is `a`, bit 3 is `b` and bit 4 is `c`. Each
  // value of `sel` is driven against all eight combinations of the three data
  // inputs, because a netlist reading the wrong source agrees with the right
  // one wherever the two sources happen to carry the same value.
  for (uint64_t sel = 0; sel < 4; ++sel) {
    for (uint64_t data = 0; data < 8; ++data) {
      const uint64_t a = data & 1U;
      const uint64_t b = (data >> 1) & 1U;
      const uint64_t c = (data >> 2) & 1U;
      const uint64_t expected = sel == 0 ? a : (sel == 1 ? b : c);
      EXPECT_EQ(EvalAigOutputs(*aig, sel | (data << 2)), expected)
          << "sel = " << sel << ", a = " << a << ", b = " << b << ", c = " << c;
    }
  }
}

}  // namespace
