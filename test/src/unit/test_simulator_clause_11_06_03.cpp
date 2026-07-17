#include <iostream>
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

// §11.6.3 is a worked example of self-determined expression sizing. It shows
// three shapes: a multiply whose size is the largest operand, a power operator
// made self-determined by an enclosing concatenation, and the same power
// operator sized instead by its assignment context. The sizing rules belong to
// §11.6.1; these tests drive the subclause's own example through the full
// pipeline and observe the simulator applying them.
namespace {

// Runs a single-module source through the full pipeline while redirecting
// stdout so a test can inspect what width the simulator gave a displayed
// expression -- the only observable for a self-determined operand that is never
// stored in a variable.
std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// `a*b` with a 4-bit and a 6-bit operand is self-determined to the larger, 6
// bits. 4'hF * 6'hA is 'h96, but the 6-bit result keeps only its low bits, so
// the displayed value is 'h16 -- the truncation the subclause illustrates. The
// product is shown directly (never assigned) so nothing widens its context.
TEST(SelfDeterminedExpressions, MultiplySizedToLargestOperandTruncates) {
  SimFixture f;
  auto out = CaptureDisplayOutput(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [5:0] b;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 6'hA;\n"
      "    $display(\"a*b=%h\", a*b);\n"
      "  end\n"
      "endmodule\n",
      f);

  EXPECT_NE(out.find("a*b=16"), std::string::npos);
}

// A concatenation makes each element self-determined, so `{a**b}` sizes a**b to
// L(a) = 4 bits regardless of the 16-bit destination. With a = 4'hF (-1 mod 16)
// raised to 6'hA, the 4-bit power is 1, and that is what lands in c. Observing
// c directly avoids any dependence on how %h pads the 16-bit result.
TEST(SelfDeterminedExpressions, PowerInsideConcatIsSelfDetermined) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [5:0] b;\n"
      "  logic [15:0] c;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 6'hA;\n"
      "    c = {a**b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0001u);
}

// The same power operator, assigned straight to the 16-bit c, is sized by that
// assignment context rather than by L(a). Evaluated at 16 bits, 4'hF ** 6'hA is
// 'hac61 -- a different result from the concatenated form above, which is the
// whole point of the example: self-determined vs. context-determined width.
TEST(SelfDeterminedExpressions, PowerAssignedDirectlyUsesContextWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [5:0] b;\n"
      "  logic [15:0] c;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 6'hA;\n"
      "    c = a**b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xac61u);
}

}  // namespace
