#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = a << 1;` lowers to today:
// `SynthLower::LowerBinaryBit` in src/synthesizer/synth_lower.cpp carries no
// arm for any of the four shift tokens, so a shift reaches `default: return
// AigGraph::kConstFalse;` on a module the synthesizer accepts without a word.
// §11.4.10 rules that the left shift moves each bit of the left operand up by
// the number of positions the right operand carries, so the netlist owes bit 0
// of `a` at bit 1 of `y` and so on up. The sweep drives `a` at 0 as well as at
// the other fifteen values, and 0 is the input that cannot fail here: a netlist
// of constant zeros agrees with a correct one there whatever it computes, so
// the fifteen non-zero values are what the case rests on.
TEST(ShiftSynthesis, LeftShiftByAConstantMovesEachBitUp) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 1"), 1,
                    [](uint64_t a, uint64_t) { return (a << 1) & 0xFu; });
}

// The test fails on a lowering that renumbers the bits in one direction only,
// which the case above passes. §11.4.10 gives `>>` the opposite direction to
// `<<`, so the netlist owes bit 1 of `a` at bit 0 of `y` and so on down, and
// the right shift arrives as its own token rather than as the left shift read
// backwards.
TEST(ShiftSynthesis, RightShiftByAConstantMovesEachBitDown) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

// The test fails on a lowering that rotates rather than shifts. A rotate agrees
// with a shift by one at the two cases above for the bits it moves, and
// disagrees here because §11.4.10 rules that the vacated bit positions are
// filled with zeros rather than with the bits that left the top: `4'b1100 << 2`
// is 4'b0000 and not 4'b0011.
TEST(ShiftSynthesis, LeftShiftFillsTheVacatedPositionsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 2"), 1,
                    [](uint64_t a, uint64_t) { return (a << 2) & 0xFu; });
}

// The test fails on a lowering that zero-fills `>>>` whatever its operand was
// declared as. §11.4.10 rules that the arithmetic right shift fills the vacated
// bit positions with the left operand's most significant (sign) bit when the
// result type is signed, so the eight values of `a` whose top bit is set are
// where this differs from `>>` and where a zero-filling lowering fails. The
// operand is declared signed and not only the target, because §11.8.1 takes an
// expression's type from its operands alone, never from a left-hand side.
TEST(ShiftSynthesis, ArithmeticRightShiftOfASignedOperandFillsWithTheSignBit) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [3:0] y",
                                      "input signed [3:0] a", "a >>> 1"),
                    1,
                    [](uint64_t a, uint64_t) { return (a >> 1) | (a & 0x8u); });
}

// The test fails on a lowering that sign-fills every `>>>`, which the case
// above passes whole. §11.4.10 rules the fill is zeros when the result type is
// unsigned, so what the vacated position carries turns on the type of the
// operand and not on the spelling of the operator, and the module below
// declares nothing signed.
TEST(ShiftSynthesis, ArithmeticRightShiftOfAnUnsignedOperandFillsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >>> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

// The test fails on a lowering that reads a constant right operand and builds
// nothing for one that arrives on a port, which the five cases above pass whole
// because each shifts by a literal. §11.4.10 asks for the shift by the value
// the right operand carries, so the netlist owes a shifter selecting between
// the four distances `s` can name rather than one fixed renumbering. Every one
// of the sixty-four combinations of the two operands is driven.
TEST(ShiftSynthesis, ShiftByAVariableAmountShiftsByTheValueItCarries) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [1:0] s", "a << s"),
                    4, [](uint64_t a, uint64_t b) { return (a << b) & 0xFu; });
}

// The test fails on a lowering that reads the result type off the shift's own
// left operand alone, which the six cases above pass because in each of them
// the shift is the whole right-hand side and no other operand stands beside it.
// §11.8.1 makes the result unsigned whenever any operand is, whatever the
// operator, so the unsigned `b` makes the whole expression unsigned. §11.4.10
// rules that the arithmetic right shift fills the vacated bit positions with
// zeros when the result type is unsigned, so the fill is zeros here although
// `a` is declared signed. Such a lowering disagrees with the case at the 128 of
// the 256 combinations whose `a` has its top bit set and agrees at the other
// 128, which is why the whole sweep is driven rather than one pair.
TEST(ShiftSynthesis, AnUnsignedOperandBesideTheShiftMakesItsResultUnsigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [3:0] b", "(a >>> 1) | b"),
      16, [](uint64_t a, uint64_t b) { return ((a >> 1) | b) & 0xFu; });
}

// The test fails on a fix that unsigns a shift whenever it stands beside
// another operand, which
// ShiftSynthesis.AnUnsignedOperandBesideTheShiftMakesItsResultUnsigned passes.
// §11.8.1 makes the result signed whenever every operand is, whatever the
// operator, so declaring `b` signed leaves the sign fill owed.
TEST(ShiftSynthesis, TwoSignedOperandsLeaveTheShiftResultSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b",
                      "(a >>> 1) | b"),
      16, [](uint64_t a, uint64_t b) {
        return ((a >> 1) | (a & 0x8u) | b) & 0xFu;
      });
}

// The test fails on a fix that folds every operand it can reach into §11.8.1's
// any-operand-unsigned rule, which the two cases above pass. §11.4.10 rules
// that a shift's right operand is always read as unsigned and leaves the
// result's signedness alone. §11.6.1 Table 11-21 marks that operand
// self-determined. The unsigned `s` therefore leaves the result signed at every
// one of the 64 combinations.
TEST(ShiftSynthesis, AnUnsignedRightOperandLeavesTheShiftResultSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [1:0] s", "a >>> s"), 4,
      [](uint64_t a, uint64_t s) {
        uint64_t fill = (a & 0x8u) != 0 ? uint64_t{0xF} : uint64_t{0};
        return ((a >> s) | (fill << (4 - s))) & 0xFu;
      });
}

// §11.6.1 Table 11-21 leaves a shift's left operand context-determined, so
// `(a + b) >>> 1` with a four-bit target carries the sum out at four bits and
// then shifts it right, filling from its own top bit, because §11.8.1 makes the
// result signed where `a` and `b` both are. The test fails on a lowering that
// reads a left operand that is not a name only at bit 0 and as zero above it,
// which shifts out the one bit it kept and drives `y` to 0 everywhere.
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
