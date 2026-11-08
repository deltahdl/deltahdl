#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

TEST(ComparisonOperandSizeSynthesis,
     AShiftComparedAgainstAWiderLiteralIsSizedToTheLiteral) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "(a << 1) == 5'd16"), 1,
                    [](uint64_t a, uint64_t) -> uint64_t {
                      return ((a << 1) & 0x1Fu) == 16 ? 1 : 0;
                    });
}

TEST(ComparisonOperandSizeSynthesis,
     AWideTargetLeavesTheComparedShiftAtItsOperandsSize) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input [3:0] a, input [3:0] b",
                        "(a << 1) == b"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a << 1) & 0xFu) == b ? 1 : 0;
      });
}

TEST(ComparisonOperandSizeSynthesis, TheWiderOfTwoComparedShiftsSizesBoth) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [4:0] c", "(a << 1) == (c << 1)"),
      32, [](uint64_t a, uint64_t c) -> uint64_t {
        return ((a << 1) & 0x1Fu) == ((c << 1) & 0x1Fu) ? 1 : 0;
      });
}

TEST(ComparisonOperandSizeSynthesis,
     TwoSignedOperandsHandTheComparedShiftASignedType) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "(a >>> 1) == b"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a >> 1) | (a & 0x8u)) == b ? 1 : 0;
      });
}

uint64_t SignExtendedFromTwoBits(uint64_t b) {
  return (b & 0x2u) != 0 ? (b | 0xCu) : b;
}

TEST(OperandExtensionSynthesis, ASignedBitwiseOperandIsSignExtended) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [1:0] b", "a ^ b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t {
        return (a ^ SignExtendedFromTwoBits(b)) & 0xFu;
      });
}

TEST(OperandExtensionSynthesis, ASignedAdditionOperandIsSignExtended) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [1:0] b", "a + b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t {
        return (a + SignExtendedFromTwoBits(b)) & 0xFu;
      });
}

TEST(OperandExtensionSynthesis, AnUnsignedOperandBesideASignedOneIsZeroFilled) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [1:0] b", "a ^ b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t { return (a ^ b) & 0xFu; });
}

uint64_t SignExtendedFromFourBits(uint64_t v) {
  return (v & 0x8u) != 0 ? (v | 0xF0u) : v;
}

TEST(OperandExtensionSynthesis, ASignedUnaryMinusOperandIsSignExtended) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [7:0] y",
                                      "input signed [3:0] a", "-a"),
                    1, [](uint64_t a, uint64_t) -> uint64_t {
                      return (0 - SignExtendedFromFourBits(a)) & 0xFFu;
                    });
}

TEST(OperandExtensionSynthesis, ASignedUnaryPlusOperandIsSignExtended) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [7:0] y",
                                      "input signed [3:0] a", "+a"),
                    1, [](uint64_t a, uint64_t) -> uint64_t {
                      return SignExtendedFromFourBits(a);
                    });
}

TEST(OperandExtensionSynthesis, ASignedBitwiseNegationOperandIsSignExtended) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [7:0] y",
                                      "input signed [3:0] a", "~a"),
                    1, [](uint64_t a, uint64_t) -> uint64_t {
                      return ~SignExtendedFromFourBits(a) & 0xFFu;
                    });
}

TEST(OperandExtensionSynthesis, AnUnsignedBitwiseNegationOperandIsZeroFilled) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input [3:0] a", "~a"), 1,
      [](uint64_t a, uint64_t) -> uint64_t { return ~a & 0xFFu; });
}

TEST(OperandExtensionSynthesis, SignedConditionalArmsAreSignExtended) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic signed [7:0] y",
                        "input signed [3:0] a, input signed [3:0] b, input c",
                        "c ? a : b"),
      32, [](uint64_t a, uint64_t bc) -> uint64_t {
        return SignExtendedFromFourBits((bc & 0x10u) != 0 ? a : bc & 0xFu);
      });
}

TEST(OperandExtensionSynthesis,
     AnUnsignedArmMakesBothConditionalArmsZeroFilled) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y",
                        "input signed [3:0] a, input [3:0] b, input c",
                        "c ? a : b"),
      32, [](uint64_t a, uint64_t bc) -> uint64_t {
        return (bc & 0x10u) != 0 ? a : bc & 0xFu;
      });
}

}  // namespace
