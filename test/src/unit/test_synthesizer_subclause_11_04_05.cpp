#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"
#include "synthesizer/aig.h"

using namespace delta;

namespace {

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
      ModuleAssigning("input [3:0] a, input [3:0] b", "a == b"), 16,
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
      ModuleAssigning("input [3:0] a, input [3:0] b", "a != b"), 16,
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
      ModuleAssigning("input [3:0] a, input [1:0] b", "a == b"), 4,
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
      ModuleAssigning("input [3:0] a, input [3:0] b", "a === b"), 16,
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
      ModuleAssigning("input [3:0] a, input [3:0] b", "a !== b"), 16,
      [](uint64_t a, uint64_t b) -> uint64_t { return a != b ? 1U : 0U; });
}

// The test fails on a synthesizer that answers `AigGraph::kConstTrue` at bit 0
// of `y`, which is what this module lowers to today. `SynthLower::MapPorts` in
// src/synthesizer/synth_lower.cpp resizes an undriven variable's bits to
// `AigGraph::kConstFalse`, so `w` is the constant zero, and §11.4.5 rules that
// the operands are compared bit for bit, which makes the comparison of zero
// against a literal with bit 64 set false. `Expr::int_val` in
// src/parser/ast_expr.h is a `uint64_t` and cannot carry
// `128'h1_0000_0000_0000_0000` at all, so the literal reads as zero in every
// position and the comparison answers true.
//
// The case does not use `ExpectAssignSweep`, because the module declares no
// input port for it to drive: both operands are constant, so the netlist's one
// output bit is an exact literal and naming `aig->outputs[0]` states the value
// rather than the gates. `EvalAigOutputs` in
// lib/cpp/test_helpers/helpers_aig_eval.h packs outputs into a `uint64_t`, so
// it cannot describe a netlist with more than 64 output bits either.
TEST(EqualitySynthesis,
     EqualityAgainstALiteralBitAboveSixtyThreeIsNotSatisfiedByZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic y);\n"
                   "  logic [127:0] w;\n"
                   "  assign y = (w == 128'h1_0000_0000_0000_0000);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
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
// §11.4.5 rules that the four equality operators "compare operands bit for
// bit", and that "If the operands are of unequal bit lengths, the smaller
// operand shall be zero-extended to the size of the larger operand".
// `128'h1_0000_0000_0000_0000` is 128 bits, so the four-bit `a` is
// zero-extended to 128 bits. Bit 64 of the extended `a` is 0 and bit 64 of the
// literal is 1, so the two differ at every value of `a` and the equality is 0
// at all sixteen of them.
//
// Over 64 positions every bit the comparison reads out of the literal is zero,
// because the only position the literal's digits set is 64, so the netlist
// drove `y` to 1 at `a` of 0 and to 0 at the other fifteen values. The whole
// sweep is what states that, since a case built on a single non-zero value of
// `a` would pass on the broken lowering.
//
// The case
// `EqualitySynthesis.EqualityAgainstALiteralBitAboveSixtyThreeIsNotSatisfiedByZero`
// above does not catch this. It already pairs a literal wider than 64 bits with
// an operand, but its operand is `logic [127:0] w`, which is wider than the
// floor, so the comparison already ran over 128 positions and the case passes.
TEST(EqualitySynthesis,
     EqualityAgainstALiteralWiderThanBothOperandsIsNeverSatisfied) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a == 128'h1_0000_0000_0000_0000"), 1,
      [](uint64_t, uint64_t) { return uint64_t{0}; });
}

}  // namespace
