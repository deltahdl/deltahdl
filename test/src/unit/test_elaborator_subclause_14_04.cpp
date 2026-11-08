#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingSkewConstExpr, LiteralSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #2 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

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

TEST(ClockingSkewConstExpr, ConstantFunctionCallSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function automatic int getskew();\n"
             "    return 3;\n"
             "  endfunction\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #(getskew()) data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

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

TEST(ClockingSkewConstExpr, OneStepSkewElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #1step data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingSkewConstExpr, VariableInputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #d data;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this clocking skew is not a constant expression; "
                            "only constants and parameters may set a skew",
                            5, "14.4"));
}

TEST(ClockingSkewConstExpr, VariableOutputSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    output #d data;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this clocking skew is not a constant expression; "
                            "only constants and parameters may set a skew",
                            5, "14.4"));
}

TEST(ClockingSkewConstExpr, VariableDefaultSkewRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, data;\n"
             "  logic [3:0] d;\n"
             "  clocking cb @(posedge clk);\n"
             "    default input #d output #0;\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this clocking skew is not a constant expression; "
                            "only constants and parameters may set a skew",
                            5, "14.4"));
}

TEST(ClockingSkewConstExpr, VariableSkewNames14_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, data;\n"
      "  logic [3:0] d;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #d data;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this clocking skew is not a constant expression; "
                            "only constants and parameters may set a skew",
                            5, "14.4"));
  for (const auto& reported : f.diag.Diagnostics()) {
    EXPECT_EQ(reported.message.find("§"), std::string::npos);
  }
}

}  // namespace
