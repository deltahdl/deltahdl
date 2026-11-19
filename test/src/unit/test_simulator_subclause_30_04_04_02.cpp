#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SimpleStateDependentPathRun, XorGateDelaysFollowTheOtherInputsState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module XORgate(a, b, out);\n"
                       "  input a, b;\n"
                       "  output out;\n"
                       "  xor x1(out, a, b);\n"
                       "  specify\n"
                       "    specparam noninvrise = 1, noninvfall = 2;\n"
                       "    specparam invertrise = 3, invertfall = 4;\n"
                       "    if (a) (b => out) = (invertrise, invertfall);\n"
                       "    if (b) (a => out) = (invertrise, invertfall);\n"
                       "    if (~a) (b => out) = (noninvrise, noninvfall);\n"
                       "    if (~b) (a => out) = (noninvrise, noninvfall);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b;\n"
                       "  wire out;\n"
                       "  XORgate g(a, b, out);\n"
                       "  always @(out) if ($time > 20)\n"
                       "    $display(\"t=%0t out=%b\", $time, out);\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    #50 b = 1;\n"
                       "    #50 a = 1;\n"
                       "    #50 b = 0;\n"
                       "    #50 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=51 out=1\nt=104 out=0\nt=153 out=1\nt=202 out=0\n");
}

std::string FullConnectionUnderCondition(std::string_view c_value) {
  std::string source =
      "module m(input c, input a, input b, output y);\n"
      "  assign y = a ^ b;\n"
      "  specify\n"
      "    if (c) (a, b *> y) = 7;\n"
      "    if (!c) (a, b *> y) = 3;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic c, a, b;\n"
      "  wire y;\n"
      "  m u(.c(c), .a(a), .b(b), .y(y));\n"
      "  always @(y) if ($time > 20)\n"
      "    $display(\"t=%0t y=%b\", $time, y);\n"
      "  initial begin\n"
      "    c = ";
  source += c_value;
  source +=
      "; a = 0; b = 0;\n"
      "    #50 a = 1;\n"
      "    #50 b = 1;\n"
      "  end\n"
      "endmodule\n";
  return source;
}

TEST(SimpleStateDependentPathRun, TrueConditionDelaysEveryFullConnectionPair) {
  SimFixture f;
  EXPECT_EQ(RunCapture(FullConnectionUnderCondition("1"), f),
            "t=57 y=1\nt=107 y=0\n");
}

TEST(SimpleStateDependentPathRun, FalseConditionWithholdsTheFullConnection) {
  SimFixture f;
  EXPECT_EQ(RunCapture(FullConnectionUnderCondition("0"), f),
            "t=53 y=1\nt=103 y=0\n");
}

}  // namespace
