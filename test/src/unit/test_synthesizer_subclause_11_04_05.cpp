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
// The operands are four bits wide because at width one an equality is a single
// exclusive nor over the two bits, so a one-bit test passes whether or not the
// comparison of the bits above it was ever built. §11.4.5 rules that the
// equality operators "compare operands bit for bit", which is a claim about
// every bit of the operands and not only the lowest.
std::string ModuleAssigning(std::string_view inputs, std::string_view rhs) {
  return "module m(" + std::string(inputs) + ", output logic [3:0] y);\n" +
         "  assign y = " + std::string(rhs) + ";\nendmodule\n";
}

// Drive every four-bit value of `a` against `b_values` values of `b` through
// the netlist the module assigning `rhs` over `inputs` lowers to, and expect
// the output word to carry `expected(a, b)`. `SynthLower::MapPorts` walks
// `mod->ports` in declaration order and allocates one AIG input per bit, so `a`
// takes bits 0 to 3 of the word handed to `EvalAigOutputs` and `b` starts at
// bit 4, whatever width `b` declares.
//
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a netlist whose every output bit is constant zero, so the sweep is what
// states which function of the operands the netlist computes. Every combination
// is driven rather than one pair, because a netlist computing some other
// function is free to agree at the pair chosen: a comparison built over the low
// bits alone agrees wherever the bits above them are equal.
//
// `expected` answers 0 or 1 rather than a value repeated across the four bits
// of `y`, which is what states the rule of §11.4.5 that "the result shall be
// 1'b0 if the comparison fails and 1'b1 if it succeeds".
void ExpectAssignSweep(std::string_view inputs, std::string_view rhs,
                       uint64_t b_values,
                       uint64_t (*expected)(uint64_t, uint64_t)) {
  SCOPED_TRACE(std::string(rhs));
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, ModuleAssigning(inputs, rhs));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t b = 0; b < b_values; ++b) {
    for (uint64_t a = 0; a < 16; ++a) {
      EXPECT_EQ(EvalAigOutputs(*aig, a | (b << 4)), expected(a, b))
          << "a = " << a << ", b = " << b;
    }
  }
}

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = (a == b);` lowers to today:
// `SynthLower::LowerBinaryBit` in src/synthesizer/synth_lower.cpp answers
// `AigGraph::kConstFalse` for every equality operator, on a module the
// synthesizer accepts without a word. Table 11-9 of §11.4.5 defines `a == b` as
// "a equal to b, result can be unknown", and §11.4.5 rules that the operands
// are compared bit for bit, so the netlist owes 1 at the 16 pairs where `a` and
// `b` hold the same value and 0 at the other 240.
TEST(EqualitySynthesis, EqualityLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      "input [3:0] a, input [3:0] b", "a == b", 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

// The test fails on a fix that reaches `==` and leaves `!=` answering constant
// zero, which the case above passes. Table 11-9 of §11.4.5 defines `a != b` as
// "a not equal to b, result can be unknown" in the one table that defines
// `a == b`, so the two are owed together, and `!=` arrives at
// `SynthLower::LowerBinaryBit` as `TokenKind::kBangEq` rather than as the
// `TokenKind::kEqEq` the case above drives.
TEST(EqualitySynthesis, InequalityLowersToTheComparisonOfItsOperands) {
  ExpectAssignSweep(
      "input [3:0] a, input [3:0] b", "a != b", 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != b ? 1U : 0U; });
}

// The test fails on a lowering that compares over the narrower operand's width
// alone, which the two cases above pass because their operands are the same
// width. §11.4.5 rules that where one or both operands are unsigned, "if the
// operands are of unequal bit lengths, the smaller operand shall be
// zero-extended to the size of the larger operand", so the two-bit `b` is
// compared against the whole of the four-bit `a`: `a` is unequal to `b`
// wherever `a` exceeds three, and a comparison of the low two bits alone
// answers 1 at four against zero.
TEST(EqualitySynthesis, EqualityOfUnequalWidthsZeroExtendsTheNarrowerOperand) {
  ExpectAssignSweep(
      "input [3:0] a, input [1:0] b", "a == b", 4,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

// §11.4.5 rules that "the result shall be 1'b0 if the comparison fails and
// 1'b1 if it succeeds", so the equality of two four-bit operands is one bit
// wide: bit 0 of `y` carries the comparison and the three bits above it are
// zero. The test fails on a lowering that answers the comparison at every bit
// index, which drives `y` to 15 where §11.4.5 asks for 1.
//
// The case names the whole four-bit output word at one equal pair and one
// unequal pair rather than sweeping, so the width of the result is what it
// claims and the function of the operands is left to the sweeps above. Those
// sweeps would report a lowering that replicates the comparison as computing
// the wrong function of `a` and `b`; this one says which value the bits above
// bit 0 carry.
TEST(EqualitySynthesis, EqualityCarriesItsResultInBitZeroAlone) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f, ModuleAssigning("input [3:0] a, input [3:0] b", "a == b"));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  // a = 5, b = 5: the comparison succeeds, so the word is 1 and not 15.
  EXPECT_EQ(EvalAigOutputs(*aig, 5U | (5U << 4)), 1U);
  // a = 5, b = 6: the comparison fails, so the word is 0 at every bit.
  EXPECT_EQ(EvalAigOutputs(*aig, 5U | (6U << 4)), 0U);
}

// The test fails on a fix that reaches the logical equality operators and
// leaves `===` answering constant zero, which the cases above pass. Table 11-9
// of §11.4.5 defines `a === b` as "a equal to b, including x and z", and
// §11.4.5 rules that for the case equality operators the result "shall always
// be a known value, either 1'b1 or 1'b0".
//
// `===` is expected to answer what `==` answers here because an `AigGraph` node
// holds two values, so no value this netlist can represent is x or z. Over the
// values it can represent, comparing with x and z included and comparing
// without them are the same function of the operands, and both are known at
// every input. `===` arrives at `SynthLower::LowerBinaryBit` as
// `TokenKind::kEqEqEq`, which is an entry a fix naming only `TokenKind::kEqEq`
// and `TokenKind::kBangEq` leaves on the `default` arm.
TEST(EqualitySynthesis,
     CaseEqualityAgreesWithLogicalEqualityOnTwoValuedOperands) {
  ExpectAssignSweep(
      "input [3:0] a, input [3:0] b", "a === b", 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a == b ? 1U : 0U; });
}

// The test fails on a fix that reaches `===` and leaves `!==` answering
// constant zero, which the case above passes. Table 11-9 of §11.4.5 defines
// `a !== b` as "a not equal to b, including x and z", and §11.4.5 rules that
// the case equality operators always yield a known value, 1'b1 or 1'b0.
//
// As with `===` above, the netlist an `AigGraph` holds carries two values per
// node, so no operand value it can represent is x or z and `!==` is the same
// function of the operands as `!=` at every one of them. `!==` arrives as
// `TokenKind::kBangEqEq`, the last of the four operators Table 11-9 names.
TEST(EqualitySynthesis,
     CaseInequalityAgreesWithLogicalInequalityOnTwoValuedOperands) {
  ExpectAssignSweep(
      "input [3:0] a, input [3:0] b", "a !== b", 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != b ? 1U : 0U; });
}

}  // namespace
