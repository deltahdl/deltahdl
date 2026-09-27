#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_synth_assign.h"
#include "helpers_synth_select.h"
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
  ExpectSelChoosesAmongThreeSources(
      "module m(input [1:0] sel, input a, input b, input c, output y);\n"
      "  assign y = (sel == 2'd0) ? a : (sel == 2'd1) ? b : c;\n"
      "endmodule");
}

// The test fails on a lowering that selects an arm by bit 0 of the condition
// alone, which answers the second arm at every even nonzero `a`. §11.4.11
// returns the first expression where the condition is true, and §11.4.7 and
// §12.4 take a value as true where it is nonzero.
TEST(ConditionalOperatorSynthesis, ANonzeroConditionSelectsTheFirstArm) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a ? b : 4'd0"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != 0 ? b : 0; });
}

// The test fails on a lowering that reads the condition at the size of the
// assignment around it, which the case above passes because its target is no
// wider than its condition. §11.6.1 Table 11-21 marks the condition of `i ? j
// : k` self-determined, so `a << 1` is four bits long and drops the bit that
// leaves the top of `a`. Read at the eight bits of `y`, it keeps that bit and
// the netlist takes the first arm at `a = 8`, where the condition is zero.
TEST(ConditionalOperatorSynthesis, TheConditionIsSizedByItself) {
  ExpectAssignSweep(ModuleAssigningTo("output logic [7:0] y", "input [3:0] a",
                                      "(a << 1) ? 8'd1 : 8'd0"),
                    1, [](uint64_t a, uint64_t) -> uint64_t {
                      return ((a << 1) & 0xFu) != 0 ? 1 : 0;
                    });
}

}  // namespace
