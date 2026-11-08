#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_synth_assign.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(EqualitySynthesis, EqualityLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a == b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

TEST(EqualitySynthesis, InequalityLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a != b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != b ? 1U : 0U; });
}

TEST(EqualitySynthesis, EqualityOfUnequalWidthsZeroExtendsTheNarrowerOperand) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [1:0] b", "a == b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

TEST(EqualitySynthesis, EqualityCarriesItsResultInBitZeroAlone) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f, ModuleAssigning("input [3:0] a, input [3:0] b", "a == b"));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(EvalAigOutputs(*aig, 5U | (5U << 4)), 1U);
  EXPECT_EQ(EvalAigOutputs(*aig, 5U | (6U << 4)), 0U);
}

TEST(EqualitySynthesis,
     CaseEqualityAgreesWithLogicalEqualityOnTwoValuedOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a === b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

TEST(EqualitySynthesis,
     CaseInequalityAgreesWithLogicalInequalityOnTwoValuedOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a !== b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != b ? 1U : 0U; });
}

TEST(EqualitySynthesis,
     EqualityAgainstALiteralBitAboveSixtyThreeIsNotSatisfiedByZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic y);\n"
                   "  logic [127:0] w;\n"
                   "  assign y = (w == 128'h1_0000_0000_0000_0000);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(EqualitySynthesis,
     EqualityAgainstALiteralWiderThanBothOperandsIsNeverSatisfied) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a == 128'h1_0000_0000_0000_0000"), 1,
      [](uint64_t, uint64_t) { return uint64_t{0}; });
}

TEST(EqualitySynthesis, ExpressionOperandIsCarriedOutAtTheOperandSize) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a - b == 4'd15"), 16,
      [](uint64_t a, uint64_t b) {
        return ((a - b) & 0xFu) == 0xFu ? uint64_t{1} : uint64_t{0};
      });
}

}  // namespace
