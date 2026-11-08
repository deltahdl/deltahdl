#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_assign.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ReductionSynthesis, ReductionAndLowersToTheConjunctionOfItsOperandBits) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "&a"), 1,
      [](uint64_t a, uint64_t) { return a == 15 ? uint64_t{1} : uint64_t{0}; });
}

TEST(ReductionSynthesis, ReductionNandLowersToTheComplementOfTheReductionAnd) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "~&a"), 1,
      [](uint64_t a, uint64_t) { return a == 15 ? uint64_t{0} : uint64_t{1}; });
}

TEST(ReductionSynthesis, ReductionOrLowersToTheDisjunctionOfItsOperandBits) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "|a"), 1,
      [](uint64_t a, uint64_t) { return a == 0 ? uint64_t{0} : uint64_t{1}; });
}

TEST(ReductionSynthesis, ReductionNorLowersToTheComplementOfTheReductionOr) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "~|a"), 1,
      [](uint64_t a, uint64_t) { return a == 0 ? uint64_t{1} : uint64_t{0}; });
}

TEST(ReductionSynthesis, ReductionXorLowersToTheParityOfItsOperandBits) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "^a"), 1,
                    [](uint64_t a, uint64_t) {
                      return (a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u;
                    });
}

TEST(ReductionSynthesis, ReductionXnorLowersToTheComplementOfTheReductionXor) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "~^a"), 1,
                    [](uint64_t a, uint64_t) {
                      return ((a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u) ^ 1u;
                    });
}

TEST(ReductionSynthesis, ReductionXnorSpelledCaretTildeLowersLikeTildeCaret) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "^~a"), 1,
                    [](uint64_t a, uint64_t) {
                      return ((a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u) ^ 1u;
                    });
}

TEST(ReductionSynthesis, AnOperandOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  assign y = &g(a);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reduction operand has no width", 3, "11.4.9"));
}

}  // namespace
