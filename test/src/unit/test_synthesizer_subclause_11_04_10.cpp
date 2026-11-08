#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

TEST(ShiftSynthesis, LeftShiftByAConstantMovesEachBitUp) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 1"), 1,
                    [](uint64_t a, uint64_t) { return (a << 1) & 0xFu; });
}

TEST(ShiftSynthesis, RightShiftByAConstantMovesEachBitDown) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

TEST(ShiftSynthesis, LeftShiftFillsTheVacatedPositionsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 2"), 1,
                    [](uint64_t a, uint64_t) { return (a << 2) & 0xFu; });
}

TEST(ShiftSynthesis, ArithmeticRightShiftOfASignedOperandFillsWithTheSignBit) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [3:0] y",
                                      "input signed [3:0] a", "a >>> 1"),
                    1,
                    [](uint64_t a, uint64_t) { return (a >> 1) | (a & 0x8u); });
}

TEST(ShiftSynthesis, ArithmeticRightShiftOfAnUnsignedOperandFillsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >>> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

TEST(ShiftSynthesis, ShiftByAVariableAmountShiftsByTheValueItCarries) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [1:0] s", "a << s"),
                    4, [](uint64_t a, uint64_t b) { return (a << b) & 0xFu; });
}

TEST(ShiftSynthesis, AnUnsignedOperandBesideTheShiftMakesItsResultUnsigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [3:0] b", "(a >>> 1) | b"),
      16, [](uint64_t a, uint64_t b) { return ((a >> 1) | b) & 0xFu; });
}

TEST(ShiftSynthesis, TwoSignedOperandsLeaveTheShiftResultSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "(a >>> 1) | b"),
      16, [](uint64_t a, uint64_t b) {
        return ((a >> 1) | (a & 0x8u) | b) & 0xFu;
      });
}

TEST(ShiftSynthesis, AnUnsignedRightOperandLeavesTheShiftResultSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [1:0] s", "a >>> s"), 4,
      [](uint64_t a, uint64_t s) {
        uint64_t fill = (a & 0x8u) != 0 ? uint64_t{0xF} : uint64_t{0};
        return ((a >> s) | (fill << (4 - s))) & 0xFu;
      });
}

TEST(ShiftSynthesis, AnExpressionLeftOperandIsShiftedWhole) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "(a + b) >>> 1"),
      16, [](uint64_t a, uint64_t b) {
        uint64_t sum = (a + b) & 0xFu;
        return ((sum >> 1) | (sum & 0x8u)) & 0xFu;
      });
}

}  // namespace
