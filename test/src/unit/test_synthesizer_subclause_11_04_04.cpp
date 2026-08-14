#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The value a four-bit raw pattern stands for when the operand carrying it is
// signed: §11.4.4 rules that where both operands are signed the expression is a
// comparison between signed values, and a four-bit two's-complement operand
// reads the patterns 8 to 15 as -8 to -1.
int64_t SignedFourBit(uint64_t raw) {
  return static_cast<int64_t>(raw) - (raw >= 8 ? 16 : 0);
}

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = a < b;` lowers to today:
// `SynthLower::LowerBinaryBit` in src/synthesizer/synth_lower.cpp answers
// `AigGraph::kConstFalse` for the relational operators, on a module the
// synthesizer accepts without a word. Table 11-8 of §11.4.4 defines `a < b` as
// "a less than b", so the netlist owes 1 at the 120 pairs where `a` is below
// `b` and 0 at the other 136.
TEST(RelationalSynthesis, LessThanLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a < b"), 16,
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a fix that reaches `a < b` and leaves `a > b` building
// nothing, which the case above passes. Table 11-8 of §11.4.4 defines `a > b`
// as "a greater than b" in the one table that defines `a < b`, so the two are
// owed together, and the greater-than arrives as its own token rather than as
// the operands of the less-than swapped.
TEST(RelationalSynthesis, GreaterThanLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a > b"), 16,
      [](uint64_t a, uint64_t b) { return a > b ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a lowering that builds `a < b` for `a <= b`, which Table
// 11-8 of §11.4.4 defines as "a less than or equal to b". The sixteen pairs
// where `a` equals `b` are what tell the two apart, since the strict and the
// non-strict comparison agree everywhere else, and the sweep drives every
// combination of the two four-bit operands so those pairs are in it by
// construction.
TEST(RelationalSynthesis, LessThanOrEqualLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a <= b"),
                    16, [](uint64_t a, uint64_t b) {
                      return a <= b ? uint64_t{1} : uint64_t{0};
                    });
}

// The test fails on a lowering that builds `a > b` for `a >= b`, which Table
// 11-8 of §11.4.4 defines as "a greater than or equal to b". As with the case
// above, the pairs where `a` equals `b` are what separate the two, and the
// greater-than-or-equal is the fourth entry of the table rather than a spelling
// of any of the other three.
TEST(RelationalSynthesis,
     GreaterThanOrEqualLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a >= b"),
                    16, [](uint64_t a, uint64_t b) {
                      return a >= b ? uint64_t{1} : uint64_t{0};
                    });
}

// The test fails on a lowering that compares the raw bit patterns whatever the
// operands were declared as. §11.4.4 rules that where both operands are signed
// the expression is a comparison between signed values, so `4'b1000` is -8 and
// stands below `4'b0111`, which is 7. A comparator that reads its operands as
// unsigned passes the four cases above whole and fails only here, because those
// modules declare no operand signed and an unsigned comparison is what §11.4.4
// owes them.
TEST(RelationalSynthesis, SignedComparisonReadsItsOperandsAsSigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input signed [3:0] b", "a < b"),
      16, [](uint64_t a, uint64_t b) {
        return SignedFourBit(a) < SignedFourBit(b) ? uint64_t{1} : uint64_t{0};
      });
}

// The test fails on a lowering that reads the comparison as signed because one
// operand was declared signed. §11.4.4 rules that "when one or both operands of
// a relational operator are unsigned, the expression shall be interpreted as a
// comparison between unsigned values", so the module below owes the comparison
// of the raw four-bit patterns even though `a` is signed. The case above and
// this one disagree at every pair whose operands differ in their top bit, so no
// lowering passes both without reading the signedness of both operands.
TEST(RelationalSynthesis, OneUnsignedOperandMakesTheComparisonUnsigned) {
  ExpectAssignSweep(
      ModuleAssigning("input signed [3:0] a, input [3:0] b", "a < b"), 16,
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a lowering that runs the comparison over fewer positions
// than the literal's size constant states. `SynthLower::CompareWidth` in
// src/synthesizer/synth_lower_compare.cpp decides how many bit positions a
// comparison runs over, and it took each operand's width from
// `SynthLower::SignalWidth`, which answers 1 for a literal because a literal is
// not a signal it holds a width for. A comparison against a literal was
// therefore carried out over the wider signal operand or 64 positions,
// whichever was larger, whatever the literal's size constant said.
//
// §11.4.4 carries the same extension rule as §11.4.5, which rules that "If the
// operands are of unequal bit lengths, the smaller operand shall be
// zero-extended to the size of the larger operand".
// `128'h1_0000_0000_0000_0000` is 128 bits, so the four-bit `a` is
// zero-extended to 128 bits. Bit 64 of the literal is 1 and every bit of the
// extended `a` from 4 up is 0, so the literal stands above `a` at all sixteen
// values and `a >= 128'h1_0000_0000_0000_0000` is 0 at every one of them.
//
// Over 64 positions the chain answered `a >= 0`, which is constant 1, so the
// netlist drove `y` to 1 at all sixteen values. This case therefore fails at
// every value of `a` where the equality case fails at one.
//
// `EqualitySynthesis.EqualityAgainstALiteralWiderThanBothOperandsIsNeverSatisfied`
// in test/src/unit/test_synthesizer_subclause_11_04_05.cpp does not stand in
// for this case. `SynthLower::CompareAtLeast` is a separate loop from
// `SynthLower::CompareEqual`, so a fix reaching one leaves the other, and that
// is why both cases are owed.
TEST(RelationalSynthesis,
     GreaterThanOrEqualAgainstALiteralWiderThanBothOperandsIsNeverSatisfied) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a >= 128'h1_0000_0000_0000_0000"), 1,
      [](uint64_t, uint64_t) { return uint64_t{0}; });
}

}  // namespace
