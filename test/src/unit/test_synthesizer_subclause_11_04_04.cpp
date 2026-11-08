#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

int64_t SignedFourBit(uint64_t raw) {
  return static_cast<int64_t>(raw) - (raw >= 8 ? 16 : 0);
}

TEST(RelationalSynthesis, LessThanLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a < b"), 16,
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

TEST(RelationalSynthesis, GreaterThanLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a > b"), 16,
      [](uint64_t a, uint64_t b) { return a > b ? uint64_t{1} : uint64_t{0}; });
}

TEST(RelationalSynthesis, LessThanOrEqualLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a <= b"),
                    16, [](uint64_t a, uint64_t b) {
                      return a <= b ? uint64_t{1} : uint64_t{0};
                    });
}

TEST(RelationalSynthesis,
     GreaterThanOrEqualLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a >= b"),
                    16, [](uint64_t a, uint64_t b) {
                      return a >= b ? uint64_t{1} : uint64_t{0};
                    });
}

TEST(RelationalSynthesis, SignedComparisonReadsItsOperandsAsSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b", "a < b"),
      16, [](uint64_t a, uint64_t b) {
        return SignedFourBit(a) < SignedFourBit(b) ? uint64_t{1} : uint64_t{0};
      });
}

TEST(RelationalSynthesis, OneUnsignedOperandMakesTheComparisonUnsigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [3:0] b", "a < b"), 16,
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

TEST(RelationalSynthesis,
     GreaterThanOrEqualAgainstALiteralWiderThanBothOperandsIsNeverSatisfied) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a >= 128'h1_0000_0000_0000_0000"), 1,
      [](uint64_t, uint64_t) { return uint64_t{0}; });
}

TEST(RelationalSynthesis, SignedExpressionOperandComparesAsSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "a - b < 0"),
      16, [](uint64_t a, uint64_t b) {
        return SignedFourBit(a) < SignedFourBit(b) ? uint64_t{1} : uint64_t{0};
      });
}

TEST(RelationalSynthesis, SignedLiteralOperandComparesAsSigned) {
  ExpectAssignSweep(ModuleAssigning("input signed [3:0] a", "a < -1"), 1,
                    [](uint64_t a, uint64_t) {
                      return SignedFourBit(a) < -1 ? uint64_t{1} : uint64_t{0};
                    });
}

TEST(RelationalSynthesis, SizedSignedLiteralIsSignExtended) {
  ExpectAssignSweep(ModuleAssigning("input signed [3:0] a", "a < 2'sb10"), 1,
                    [](uint64_t a, uint64_t) {
                      return SignedFourBit(a) < -2 ? uint64_t{1} : uint64_t{0};
                    });
}

}  // namespace
