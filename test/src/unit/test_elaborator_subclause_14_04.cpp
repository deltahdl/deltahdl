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

// §14.4: a localparam is a constant-expression form (§11.2.1) and, like a
// parameter, is an acceptable skew. Confirms the constant-expression check
// resolves the localparam through the module's constant scope.
TEST(ClockingSkewConstExpr, LocalparamSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam SK = 4;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #SK data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: a constant function call (§11.2.1) is a constant expression, hence a
// legal skew. The call cannot always be folded to an integer at this check, so
// the rule must accept it as constant rather than rejecting it as non-constant.
TEST(ClockingSkewConstExpr, ConstantFunctionCallSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function automatic int getskew();\n"
             "    return 3;\n"
             "  endfunction\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #getskew() data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.4: the constant-expression requirement also governs the block-wide
// default skews (the `default input/output` item), which the elaborator checks
// at a separate site from the per-signal skews. Constant default skews on both
// directions must elaborate cleanly.
TEST(ClockingSkewConstExpr, DefaultBlockSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter IN_SK = 2;\n"
             "  localparam OUT_SK = 3;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #IN_SK output #OUT_SK;\n"
             "    input data;\n"
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
