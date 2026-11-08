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

TEST(LogicalOperatorSynthesis, ImplicationIsZeroOnlyFromNonzeroToZero) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a -> b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == 0 || b != 0; });
}

TEST(LogicalOperatorSynthesis, EquivalenceIsOneWhereBothOperandsAgree) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a <-> b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return (a != 0) == (b != 0); });
}

TEST(LogicalOperatorSynthesis, AnOperandIsSizedByItself) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input [3:0] a", "!(a << 1)"),
      1, [](uint64_t a, uint64_t) -> uint64_t {
        return ((a << 1) & 0xFu) == 0 ? 1 : 0;
      });
}

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
