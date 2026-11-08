#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

TEST(WildcardEqualitySynthesis,
     WildcardEqualityTreatsTheRightOperandsWildcardsAsDontCare) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a ==? 4'b10?z"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return (((a >> 3) & 1U) == 1U && ((a >> 2) & 1U) == 0U) ? 1U : 0U;
      });
}

TEST(WildcardEqualitySynthesis,
     WildcardInequalityIsTheNegationOfWildcardEquality) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a !=? 4'b10?z"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return (((a >> 3) & 1U) == 1U && ((a >> 2) & 1U) == 0U) ? 0U : 1U;
      });
}

TEST(WildcardEqualitySynthesis,
     WildcardEqualityWithANonLiteralRightOperandIsReported) {
  ExpectAssignReported(
      "input [3:0] a, input [3:0] b", "a ==? b",
      "'a ==? b' with a right operand that is not an integer literal has no "
      "lowering in the synthesizer",
      "11.4.6");
}

TEST(WildcardEqualitySynthesis,
     WildcardInequalityWithANonLiteralRightOperandIsReported) {
  ExpectAssignReported(
      "input [3:0] a, input [3:0] b", "a !=? b",
      "'a !=? b' with a right operand that is not an integer literal has no "
      "lowering in the synthesizer",
      "11.4.6");
}

TEST(WildcardEqualitySynthesis,
     WildcardEqualityWithAnUnbasedLiteralComparesIt) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a ==? 5"), 1,
      [](uint64_t a, uint64_t) -> uint64_t { return a == 5U ? 1U : 0U; });
}

}  // namespace
