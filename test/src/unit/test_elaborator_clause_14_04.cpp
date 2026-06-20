#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §14.4: "A skew shall be a constant expression and can be specified as a
// parameter." A plain integer-literal skew is the simplest constant form and
// must elaborate cleanly.
TEST(ClockingSkewConstExpr, LiteralSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #2 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: a parameter is explicitly permitted as a skew.
TEST(ClockingSkewConstExpr, ParameterSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter SK = 3;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #SK data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: an expression built only from constants (here a parameter scaled by a
// literal) is still a constant expression and is accepted.
TEST(ClockingSkewConstExpr, ConstantArithmeticSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter SK = 3;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #(SK + 1) data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: the 1step skew is a valid constant skew form; the constant-expression
// check must accept it rather than flagging it as non-constant.
TEST(ClockingSkewConstExpr, OneStepSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #1step data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: a skew that references a variable is not a constant expression and is
// rejected.
TEST(ClockingSkewConstExpr, VariableInputSkewRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #d data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: the same constant-expression requirement applies to an output skew.
TEST(ClockingSkewConstExpr, VariableOutputSkewRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #d data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: the requirement covers the block-wide default skews as well as
// per-signal skews.
TEST(ClockingSkewConstExpr, VariableDefaultSkewRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #d output #0;\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
