#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The source of a module whose continuous assignment drives the four-bit output
// `y` from `rhs`, over the input ports `inputs` declares.
//
// The operands are four bits wide because at width one every relational
// operator of Table 11-8 collapses to a single gate over the two bits, so a
// one-bit test passes whether or not the comparison of the bits above it was
// ever built.
std::string ModuleAssigning(std::string_view inputs, std::string_view rhs) {
  return std::string("module m(") + std::string(inputs) +
         ", output logic [3:0] y);\n  assign y = " + std::string(rhs) +
         ";\nendmodule\n";
}

// Drive every four-bit value of `a` against every four-bit value of `b` through
// the netlist `src` lowers to, and expect the output to carry `expected(a, b)`.
// `SynthLower::MapPorts` walks `mod->ports` in declaration order and allocates
// one AIG input per bit, so `a` takes bits 0 to 3 of the word handed to
// `EvalAigOutputs` and `b` takes bits 4 to 7.
//
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a netlist whose every output bit is constant zero, so the sweep is what
// states which function of the operands the netlist computes. All 256
// combinations are driven rather than one pair, because a netlist computing
// some other function is free to agree at the pair chosen: a comparator wired
// wrongly above its low bits agrees wherever those bits decide the answer.
//
// `expected` answers 0 or 1 rather than a value repeated across the four bits
// of `y`, which is what states the rule of §11.4.4 that a relational expression
// "shall yield 1'b0 if the specified relation is false or 1'b1 if it is true":
// bit 0 carries the comparison and the three bits above it are zero.
void ExpectAssignSweep(const std::string& src,
                       uint64_t (*expected)(uint64_t, uint64_t)) {
  SCOPED_TRACE(src);
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, src);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    for (uint64_t b = 0; b < 16; ++b) {
      EXPECT_EQ(EvalAigOutputs(*aig, a | (b << 4)), expected(a, b))
          << "a = " << a << ", b = " << b;
    }
  }
}

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
      ModuleAssigning("input [3:0] a, input [3:0] b", "a < b"),
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a fix that reaches `a < b` and leaves `a > b` building
// nothing, which the case above passes. Table 11-8 of §11.4.4 defines `a > b`
// as "a greater than b" in the one table that defines `a < b`, so the two are
// owed together, and the greater-than arrives as its own token rather than as
// the operands of the less-than swapped.
TEST(RelationalSynthesis, GreaterThanLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a, input [3:0] b", "a > b"),
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
                    [](uint64_t a, uint64_t b) {
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
                    [](uint64_t a, uint64_t b) {
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
      [](uint64_t a, uint64_t b) {
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
      ModuleAssigning("input signed [3:0] a, input [3:0] b", "a < b"),
      [](uint64_t a, uint64_t b) { return a < b ? uint64_t{1} : uint64_t{0}; });
}

}  // namespace
