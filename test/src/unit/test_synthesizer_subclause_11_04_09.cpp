#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// Every case below fails on a netlist that drives `y` with `a` bit for bit,
// which is what the synthesizer answers for a reduction operator today.
// `SynthLower::LowerUnaryBit` in src/synthesizer/synth_lower.cpp handles
// `TokenKind::kTilde` and `TokenKind::kBang` and then ends `return operand;`,
// so every other unary operator answers the operand's own bit at the index
// asked for while the run reports success. §11.4.9 rules that "The unary
// reduction operators shall perform a bitwise operation on a single operand to
// produce a single-bit result", so the netlist owes the answer in bit 0 and
// zero in bits 1 to 3, which is why each case compares the whole four-bit
// output word rather than its low bit.
//
// Each case sweeps all sixteen values of `a`, because `&a`, `|a` and `^a` each
// agree with a lowering that copies the operand at an all-zeros operand, so a
// case built on that one value passes whether the operator is lowered or not.
// Table 11-19 of §11.4.9 gives the worked answers over `4'b0000`, `4'b1111`,
// `4'b0110` and `4'b1000`, and all four values are inside the sweep.

// The test fails on any lowering that builds nothing for a reduction AND, since
// this is the first case. §11.4.9 gives the reduction AND as the conjunction of
// the operand bits, so the netlist owes 1 for the one operand value whose four
// bits are all set and 0 for the other fifteen.
TEST(ReductionSynthesis, ReductionAndLowersToTheConjunctionOfItsOperandBits) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "&a"), 1,
      [](uint64_t a, uint64_t) { return a == 15 ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a fix that reaches `TokenKind::kAmp` and leaves
// `TokenKind::kTildeAmp` on the fall-through of `SynthLower::LowerUnaryBit`,
// which ReductionSynthesis.ReductionAndLowersToTheConjunctionOfItsOperandBits
// passes. §11.4.9 rules that "For reduction NAND, reduction NOR, and reduction
// XNOR operators, the result shall be computed by inverting the result of the
// reduction AND, reduction OR, and reduction XOR operation, respectively", so
// the expected value is the complement of the case above at every operand.
TEST(ReductionSynthesis, ReductionNandLowersToTheComplementOfTheReductionAnd) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "~&a"), 1,
      [](uint64_t a, uint64_t) { return a == 15 ? uint64_t{0} : uint64_t{1}; });
}

// The test fails on a fix that reaches the two AND spellings and leaves
// `TokenKind::kPipe` on the fall-through, which the two cases above pass.
// §11.4.9 gives the reduction OR as the disjunction of the operand bits, so the
// netlist owes 0 for the one all-zeros operand and 1 for the other fifteen,
// which is the answer of the reduction AND at fourteen of the sixteen values.
TEST(ReductionSynthesis, ReductionOrLowersToTheDisjunctionOfItsOperandBits) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "|a"), 1,
      [](uint64_t a, uint64_t) { return a == 0 ? uint64_t{0} : uint64_t{1}; });
}

// The test fails on a fix that reaches `TokenKind::kPipe` and leaves
// `TokenKind::kTildePipe` on the fall-through, which the three cases above
// pass. §11.4.9 rules that the reduction NOR is the reduction OR inverted, so
// the expected value is the complement of the case above at every operand.
TEST(ReductionSynthesis, ReductionNorLowersToTheComplementOfTheReductionOr) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "~|a"), 1,
      [](uint64_t a, uint64_t) { return a == 0 ? uint64_t{1} : uint64_t{0}; });
}

// The test fails on a fix that reaches the AND and OR spellings and leaves
// `TokenKind::kCaret` on the fall-through, which the four cases above pass.
// §11.4.9 gives the reduction XOR as the parity of the operand bits, and Table
// 11-19 answers it 0 over `4'b0110` and 1 over `4'b1000`, which is a pair of
// operands the four cases above cannot tell apart: the reduction AND, NAND, OR
// and NOR each answer both of them alike.
TEST(ReductionSynthesis, ReductionXorLowersToTheParityOfItsOperandBits) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "^a"), 1,
                    [](uint64_t a, uint64_t) {
                      return (a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u;
                    });
}

// The test fails on a fix that reaches `TokenKind::kCaret` and leaves
// `TokenKind::kTildeCaret` on the fall-through, which the five cases above
// pass. §11.4.9 rules that the reduction XNOR is the reduction XOR inverted, so
// the expected value is the complement of the case above at every operand.
TEST(ReductionSynthesis, ReductionXnorLowersToTheComplementOfTheReductionXor) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "~^a"), 1,
                    [](uint64_t a, uint64_t) {
                      return ((a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u) ^ 1u;
                    });
}

// The test fails on a fix that names `TokenKind::kTildeCaret` and not
// `TokenKind::kCaretTilde`, which
// ReductionSynthesis.ReductionXnorLowersToTheComplementOfTheReductionXor
// passes. Table 11-1 of §11.3 lists `~^` and `^~` as one operator, while
// `PrefixBp` in src/parser/expr_parser.cpp accepts the two token kinds in
// separate `case` labels, so the two spellings arrive at the synthesizer as
// different `expr->op` values and each has to be answered.
TEST(ReductionSynthesis, ReductionXnorSpelledCaretTildeLowersLikeTildeCaret) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "^~a"), 1,
                    [](uint64_t a, uint64_t) {
                      return ((a ^ (a >> 1) ^ (a >> 2) ^ (a >> 3)) & 1u) ^ 1u;
                    });
}

// The test fails on a fix that folds the operator across a guessed width, which
// the seven cases above pass because each declares its operand `[3:0]` and asks
// nothing about an operand the synthesizer cannot measure. §11.4.9 folds the
// operator across the bits of the operand, so an operand whose width the
// synthesizer cannot answer is one it cannot fold over. A fix measuring this
// operand too wide answers a reduction AND of constant zero, which is the
// silent wrong answer the seven cases above are about, narrowed rather than
// removed.
TEST(ReductionSynthesis, AnOperandOfUnknownWidthIsReported) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "&(a + b)",
                       "reduction operand has no width", "11.4.9");
}

}  // namespace
