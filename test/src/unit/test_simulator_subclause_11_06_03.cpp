#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "fixture_simulator.h"

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

TEST(SelfDeterminedExpressions, PowerInsideConcatIsSelfDetermined) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "c");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0001u);
}

TEST(SelfDeterminedExpressions, PowerAssignedDirectlyUsesContextWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "c");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xac61u);
}

}  // namespace
