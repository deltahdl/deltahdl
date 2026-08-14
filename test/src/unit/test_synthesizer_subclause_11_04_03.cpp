#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = a + b;` lowers to today on a
// module the synthesizer accepts without a word. Table 11-3 of §11.4.3 defines
// `a + b` as "a plus b", so the netlist owes the sum of the two operands,
// truncated to the four bits `y` declares.
TEST(ArithmeticSynthesis, AdditionLowersToTheSumOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a + b"),
                    16, [](uint64_t a, uint64_t b) { return (a + b) & 0xFU; });
}

// The test fails on a fix that reaches addition and leaves subtraction building
// nothing, which the case above passes. Table 11-3 of §11.4.3 defines `a - b`
// as "a minus b" in the one table that defines `a + b`, so the two are owed
// together. The expected value wraps at the width of `y`, so zero minus one
// leaves fifteen.
TEST(ArithmeticSynthesis, SubtractionLowersToTheDifferenceOfItsOperands) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [3:0] b", "a - b"),
                    16, [](uint64_t a, uint64_t b) { return (a - b) & 0xFU; });
}

// The test fails when `y++` has a lowering and `a + 4'd1` has none, which is
// the state of the synthesizer today. §11.4.2 rules that "these increment and
// decrement assignment operators behave as blocking assignments", which makes
// the two spellings one operation, and
// IncrementSynthesis.PostfixIncrementLowersAsABlockingAssignment in
// test/src/unit/test_synthesizer_subclause_11_04_02.cpp already expects
// `(a + 1) & 0xF` of `y++` over the same four-bit operand.
//
// The module declares `a` alone, so there is no second input to drive and the
// sweep runs over the sixteen values of `a`.
TEST(ArithmeticSynthesis, AdditionByOneAgreesWithTheIncrementOfTheSameOperand) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a + 4'd1"), 1,
                    [](uint64_t a, uint64_t) { return (a + 1) & 0xFU; });
}

// The test fails when `assign y = a * b;` lowers to a netlist rather than to a
// report: `y` comes back constant zero and nothing says the multiply was
// dropped. Table 11-3 of §11.4.3 defines `a * b` as "a multiplied by b", and
// this synthesizer builds no multiplier, so what the design is owed is the
// report.
//
// The multiply, the divide, the modulo and the power get one case each rather
// than one case between them, because a fix that reports the multiply and
// leaves `TokenKind::kPower` on the `default` arm passes any test that names
// only the multiply. Each case names the words Table 11-3 gives its own
// operator, so no one of them passes on another operator's report.
TEST(ArithmeticSynthesis, MultiplicationIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a * b",
                       "a multiplied by b", "11.4.3");
}

// The test fails when `assign y = a / b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a / b` as "a divided by b", and
// §11.4.3 goes on to rule that the result is x when the second operand is zero,
// which is a value the two-valued netlist an AigGraph holds cannot carry.
TEST(ArithmeticSynthesis, DivisionIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a / b",
                       "a divided by b", "11.4.3");
}

// The test fails when `assign y = a % b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a % b` as "a modulo b", and the modulo
// arrives as `TokenKind::kPercent` rather than as the `TokenKind::kSlash` the
// case above drives, so a fix naming only the divide passes that one and fails
// this one.
TEST(ArithmeticSynthesis, ModulusIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a % b", "a modulo b",
                       "11.4.3");
}

// The test fails when `assign y = a ** b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a ** b` as "a to the power of b", and
// the power arrives as `TokenKind::kPower`, which is the entry of the table a
// fix naming the three single-character operators leaves on the `default` arm.
TEST(ArithmeticSynthesis, PowerIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("input [3:0] a, input [3:0] b", "a ** b",
                       "a to the power of b", "11.4.3");
}

// The test fails on a synthesizer that drives `y` with `a` unchanged, which is
// what `assign y = -a;` lowers to today. `SynthLower::LowerUnaryBit` in
// src/synthesizer/synth_lower.cpp handles `TokenKind::kTilde` and
// `TokenKind::kBang` and then ends `return operand;`, so every other unary
// operator answers the operand's own bit at the index asked for. Table 11-6 of
// §11.4.3 gives `-m` as "Unary minus m", and §11.4.3.1 rules that "Signed
// values, except for those assigned to real variables, shall use a
// two's-complement representation". Bit `bit` of the negation depends on every
// operand bit below it, so no lowering reading the operand at `bit` alone can
// answer it.
//
// The four cases above drive binary operators, which reach
// `SynthLower::LowerAddSubBit` and the reports rather than the unary arm, so
// none of them says anything about a unary operator. The whole sixteen-value
// sweep is what makes this case able to fail: `-a` and a lowering that copies
// the operand agree at `a == 0`, so a case built on that one value passes
// whether the negation is lowered or not.
TEST(ArithmeticSynthesis, UnaryMinusLowersToTheTwosComplementOfItsOperand) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "-a"), 1,
                    [](uint64_t a, uint64_t) { return (16u - a) & 0xFu; });
}

// The test passes today and holds the one arm of the fall-through that is right
// against a fix that changes it. Table 11-6 of §11.4.3 gives `+m` as "Unary
// plus m (same as m)", so `return operand;` is the answer this operator is
// owed, and the case above is the one that says the same statement is the
// wrong answer for `-m`. No earlier case pins any unary operator down, so a fix
// that gives `TokenKind::kPlus` a negation, or that reports it as unhandled,
// breaks nothing before this one.
TEST(ArithmeticSynthesis, UnaryPlusLowersToItsOperandUnchanged) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "+a"), 1,
                    [](uint64_t a, uint64_t) { return a; });
}

}  // namespace
