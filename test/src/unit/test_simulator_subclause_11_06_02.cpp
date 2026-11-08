#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(ExpressionBitLengthProblem, InterimAddSizedToOperandsLosesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f, "answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(ExpressionBitLengthProblem, WideningInterimWithIntegerPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f, "answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLengthProblem, WideningInterimWithParameterPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  parameter integer w = 0;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + w) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f, "answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLengthProblem, WideningInterimWithLocalparamPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  localparam integer w = 0;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + w) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f, "answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLengthProblem, AssignmentLhsWidthSizesInterimPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

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
