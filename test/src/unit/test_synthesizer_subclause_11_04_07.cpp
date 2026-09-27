#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_assign.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(LogicalOperators, NotGate) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = !a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
}

// Every case below fails on a lowering that reads the truth value of an operand
// from its bit 0 alone, which answers every even nonzero operand as false.
// §11.4.7 makes a value true where it is nonzero: its Example 1 gives `alpha &&
// beta` with `alpha` holding 237 and `beta` 0 as 0 and `alpha || beta` as 1,
// and its Example 3 gives `if (!inword)` as the same logic as `if (inword ==
// 0)`. The operands are four bits wide and every combination is driven, so the
// eight even nonzero values are among them.

TEST(LogicalOperatorSynthesis, LogicalNegationIsOneOnlyForZero) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "!a"), 1,
                    [](uint64_t a, uint64_t) -> uint64_t { return a == 0; });
}

TEST(LogicalOperatorSynthesis, LogicalAndIsOneWhereBothOperandsAreNonzero) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a && b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != 0 && b != 0; });
}

TEST(LogicalOperatorSynthesis, LogicalOrIsOneWhereEitherOperandIsNonzero) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a || b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != 0 || b != 0; });
}

// §11.4.7 makes `expression1 -> expression2` logically equivalent to
// `(!expression1 || expression2)`.
TEST(LogicalOperatorSynthesis, ImplicationIsZeroOnlyFromNonzeroToZero) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a -> b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == 0 || b != 0; });
}

// §11.4.7 makes `expression1 <-> expression2` logically equivalent to
// `((expression1 -> expression2) && (expression2 -> expression1))`.
TEST(LogicalOperatorSynthesis, EquivalenceIsOneWhereBothOperandsAgree) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a <-> b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return (a != 0) == (b != 0); });
}

// The test fails on a lowering that reads an operand at the size of the
// assignment around it, which the cases above pass because their target is no
// wider than their operands. §11.6.1 Table 11-21 marks the operands of the
// logical operators self-determined, so `a << 1` is four bits long and drops
// the bit that leaves the top of `a`. Read at the eight bits of `y`, it keeps
// that bit and the netlist answers 0 at `a = 8`, where the operand is zero.
TEST(LogicalOperatorSynthesis, AnOperandIsSizedByItself) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input [3:0] a", "!(a << 1)"),
      1, [](uint64_t a, uint64_t) -> uint64_t {
        return ((a << 1) & 0xFu) == 0 ? 1 : 0;
      });
}

// The test fails on a fix that reads an operand of unknown width across a
// guessed width and reports nothing. Whether a value is nonzero turns on every
// bit it has, so an operand whose width the synthesizer cannot answer is one it
// cannot test. `SynthLower::ExprWidth` reads no function's declaration, so a
// call is such an operand.
TEST(LogicalOperatorSynthesis, AnOperandOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  assign y = !g(a);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand has no width in the synthesizer", 3,
                            "11.4.7"));
}

}  // namespace
