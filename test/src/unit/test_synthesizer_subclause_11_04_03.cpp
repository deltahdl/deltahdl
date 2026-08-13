#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The source of a module whose continuous assignment drives the four-bit output
// `y` from `rhs`, over the input ports `inputs` declares. The whole assignment
// is on line 2, which is the line a report about it stands at.
//
// The operands are four bits wide because at width one a carry chain is a
// single exclusive or, so a one-bit test passes whether or not the carry into
// the bit above it was ever built.
std::string ModuleAssigning(std::string_view inputs, std::string_view rhs) {
  return std::string("module m(") + std::string(inputs) +
         ", output logic [3:0] y);\n  assign y = " + std::string(rhs) +
         ";\nendmodule\n";
}

// Drive every four-bit value of `a` against `b_values` values of `b` through
// the netlist `src` lowers to, and expect the output to carry `expected(a, b)`.
// `SynthLower::MapPorts` walks `mod->ports` in declaration order, so `a` takes
// bits 0 to 3 of the word handed to `EvalAigOutputs` and `b` takes bits 4 to 7.
//
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a netlist whose every output bit is constant zero, so the sweep is what
// states which function of the operands the netlist computes. All 256
// combinations are driven rather than one pair, because a netlist computing
// some other function is free to agree at the pair chosen: a ripple-carry chain
// wired wrongly above its low bits agrees at small values and disagrees at
// large ones.
void ExpectAssignSweep(const std::string& src, uint64_t b_values,
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
    for (uint64_t b = 0; b < b_values; ++b) {
      EXPECT_EQ(EvalAigOutputs(*aig, a | (b << 4)), expected(a, b))
          << "a = " << a << ", b = " << b;
    }
  }
}

// Expect the module assigning `rhs` to two four-bit inputs to be refused rather
// than lowered, and expect the error containing `message` to stand at line 2
// under §11.4.3. `SynthLower::Lower` answering a graph is the failure this
// guards against, because that graph carries an output the design never asked
// for and nothing tells the reader an operator was dropped.
void ExpectAssignReported(std::string_view rhs, std::string_view message) {
  SCOPED_TRACE(std::string(rhs));
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f, ModuleAssigning("input [3:0] a, input [3:0] b", rhs));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 2, "11.4.3"));
}

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
  ExpectAssignReported("a * b", "a multiplied by b");
}

// The test fails when `assign y = a / b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a / b` as "a divided by b", and
// §11.4.3 goes on to rule that the result is x when the second operand is zero,
// which is a value the two-valued netlist an AigGraph holds cannot carry.
TEST(ArithmeticSynthesis, DivisionIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("a / b", "a divided by b");
}

// The test fails when `assign y = a % b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a % b` as "a modulo b", and the modulo
// arrives as `TokenKind::kPercent` rather than as the `TokenKind::kSlash` the
// case above drives, so a fix naming only the divide passes that one and fails
// this one.
TEST(ArithmeticSynthesis, ModulusIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("a % b", "a modulo b");
}

// The test fails when `assign y = a ** b;` lowers to a netlist rather than to a
// report. Table 11-3 of §11.4.3 defines `a ** b` as "a to the power of b", and
// the power arrives as `TokenKind::kPower`, which is the entry of the table a
// fix naming the three single-character operators leaves on the `default` arm.
TEST(ArithmeticSynthesis, PowerIsReportedRatherThanLoweredToZero) {
  ExpectAssignReported("a ** b", "a to the power of b");
}

}  // namespace
