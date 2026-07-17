#include <iostream>
#include <sstream>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

// §11.6.2 illustrates the expression bit-length problem: during evaluation an
// interim result takes the size of the largest operand, and in an assignment
// the left-hand side is one of those operands. These tests observe the
// simulator applying that rule on the subclause's own examples.
namespace {

// Runs a single-module source through the full pipeline while redirecting
// stdout so the test can inspect the width the simulator gave a displayed
// expression -- the observable that reveals context-determined widening.
std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// The interim (a + b) is self-determined to 16 bits — the width of the largest
// operand, no wider than the 16-bit destination — so the carry out of the add
// is lost before the right shift, exactly the problem the subclause describes.
TEST(ExpressionBitLengthProblem, InterimAddSizedToOperandsLosesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

// Adding an integer-sized 0 brings a wider operand into the expression, so the
// interim sum is evaluated with enough bits to keep the carry and the shift
// produces the intended result.
TEST(ExpressionBitLengthProblem, WideningInterimWithIntegerPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

// Same widening, but the wide operand is supplied by a parameter rather than a
// literal 0. A parameter reference reaches the evaluator through a different
// path than a folded literal, yet its integer width feeds the same
// largest-operand sizing, so the interim sum keeps the carry across the shift.
TEST(ExpressionBitLengthProblem, WideningInterimWithParameterPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer w = 0;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + w) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

// The localparam form of the same constant-widening input: a localparam is
// declared and elaborated through a distinct path from a parameter, but as an
// integer-width operand it likewise sizes the interim sum wide enough to
// preserve the carry.
TEST(ExpressionBitLengthProblem, WideningInterimWithLocalparamPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam integer w = 0;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + w) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

// The other half of the rule: in an assignment the left-hand side counts as one
// of the operands that size the interim result. Here the destination is one bit
// wider than both addends, so the add is evaluated with that extra bit and the
// carry survives — the affirmative counterpart to the equal-width case above.
TEST(ExpressionBitLengthProblem, AssignmentLhsWidthSizesInterimPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// In `c ? (a & b) : d`, a & b is self-determined to 4 bits, but the conditional
// expression sizes its operands to the largest of the two branches. Because d
// is declared 5 bits wide, the selected a & b result is widened to 5 bits: the
// %b display prints "01000" -- five characters -- rather than the four-bit
// "1000" it would show if a & b kept its self-determined width. This is the
// subclause's `bitlength` module verbatim, so the widening is driven entirely
// by the real declarations flowing through the full pipeline.
TEST(ExpressionBitLengthProblem, ConditionalContextWidensNarrowBranch) {
  SimFixture f;
  auto out = CaptureDisplayOutput(
      "module bitlength;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [4:0] d;\n"
      "  initial begin\n"
      "    a = 9;\n"
      "    b = 8;\n"
      "    c = 1;\n"
      "    $display(\"answer = %b\", c ? (a & b) : d);\n"
      "  end\n"
      "endmodule\n",
      f);

  EXPECT_NE(out.find("answer = 01000"), std::string::npos);
}

}  // namespace
