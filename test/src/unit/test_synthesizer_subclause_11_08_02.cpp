#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The test fails on a lowering that cuts a shift standing as an operand of a
// comparison to the width of the assignment's target, which is four bits here,
// rather than to the size of the comparison's operands. §11.6.1 Table 11-21
// sizes both operands of `==` to the larger of their lengths, five bits for the
// literal, and §11.8.2 propagates that size down to the context-determined left
// operand of the shift. `8 << 1` therefore keeps its top bit as 16 and equals
// the literal. `a = 8` is the one value where the two lowerings disagree: every
// other value of `a` shifts to something other than 16 in five bits as well as
// in four.
TEST(ComparisonOperandSizeSynthesis,
     AShiftComparedAgainstAWiderLiteralIsSizedToTheLiteral) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "(a << 1) == 5'd16"), 1,
                    [](uint64_t a, uint64_t) -> uint64_t {
                      return ((a << 1) & 0x1Fu) == 16 ? 1 : 0;
                    });
}

// The test fails on a lowering that sizes a comparison's operands from the
// assignment's target, eight bits here, which the case above passes when the
// target is the wider of the two. §11.8.2 leaves the operands of a relational
// or equality operator to be sized by each other and not by the context the
// one-bit result stands in, so with `a` and `b` both four bits wide `a << 1`
// loses the bit that leaves the top. A lowering that keeps it answers 0 at the
// eight values of `a` with bit 3 set wherever `b` equals the four-bit shift.
TEST(ComparisonOperandSizeSynthesis,
     AWideTargetLeavesTheComparedShiftAtItsOperandsSize) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input [3:0] a, input [3:0] b",
                        "(a << 1) == b"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a << 1) & 0xFu) == b ? 1 : 0;
      });
}

// The test fails on a lowering that finds no width in a shift, which the two
// cases above pass because a literal or a signal stands on the other side.
// §11.6.1 Table 11-21 gives a shift the length of its left operand, so `c << 1`
// is five bits long and sizes both operands to five, and `a << 1` keeps the bit
// that leaves the top of the four-bit `a`. A lowering that cuts each shift to
// its own left operand disagrees at every `a` from 8 to 15, where `c` repeats
// the low four bits of `a`.
TEST(ComparisonOperandSizeSynthesis, TheWiderOfTwoComparedShiftsSizesBoth) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [4:0] c", "(a << 1) == (c << 1)"),
      32, [](uint64_t a, uint64_t c) -> uint64_t {
        return ((a << 1) & 0x1Fu) == ((c << 1) & 0x1Fu) ? 1 : 0;
      });
}

// The test fails on a lowering that hands a compared shift the type of the
// comparison's one-bit result, which §11.8.1 rules unsigned, rather than the
// type of the comparison's operands. §11.8.2 propagates the type down with the
// size, and §11.8.1 makes the operands' type signed where both are, so `a >>>
// 1` fills its vacated top position with the sign bit of `a` as §11.4.10 asks.
// A zero-filling lowering disagrees wherever `a` has bit 3 set and `b` equals
// one of the two fills.
TEST(ComparisonOperandSizeSynthesis,
     TwoSignedOperandsHandTheComparedShiftASignedType) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "(a >>> 1) == b"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a >> 1) | (a & 0x8u)) == b ? 1 : 0;
      });
}

// The value `b` stands for in a four-bit signed context: its two bits with the
// top one copied into bits 3 and 2.
uint64_t SignExtendedFromTwoBits(uint64_t b) {
  return (b & 0x2u) != 0 ? (b | 0xCu) : b;
}

// The test fails on a lowering that zero-extends a signed operand of a binary
// operator narrower than the expression. §11.8.1 makes `a ^ b` signed with
// both operands signed, §11.6.1 Table 11-21 makes both operands of `^`
// context-determined, and §11.8.2 extends each to the expression's four bits
// by its sign where the propagated type is signed. A zero-extending lowering
// disagrees wherever `b` has its top bit set.
TEST(OperandExtensionSynthesis, ASignedBitwiseOperandIsSignExtended) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [1:0] b", "a ^ b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t {
        return (a ^ SignExtendedFromTwoBits(b)) & 0xFu;
      });
}

// The same of `+`, whose operands Table 11-21 makes context-determined too:
// `b` = 2'b10 is -2, so `a + b` subtracts 2 where a zero-extended `b` adds 2.
TEST(OperandExtensionSynthesis, ASignedAdditionOperandIsSignExtended) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [1:0] b", "a + b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t {
        return (a + SignExtendedFromTwoBits(b)) & 0xFu;
      });
}

// §11.8.1 makes the expression unsigned where either operand is, so an
// unsigned `b` beside a signed `a` is zero-extended. The test fails on a
// lowering that sign-extends every narrower operand.
TEST(OperandExtensionSynthesis, AnUnsignedOperandBesideASignedOneIsZeroFilled) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [1:0] b", "a ^ b"), 4,
      [](uint64_t a, uint64_t b) -> uint64_t { return (a ^ b) & 0xFu; });
}

}  // namespace
