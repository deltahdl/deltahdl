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

}  // namespace
