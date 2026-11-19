#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IfnoneConditionSim, FullPathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    ifnone (a, b *> c) = 10;\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IfnoneConditionSim, LoneIfnonePathDelaysLikeAnUnconditionalPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybuf(input a, output y);\n"
                       "  assign y = a;\n"
                       "  specify\n"
                       "    ifnone (a => y) = 5;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a;\n"
                       "  wire y;\n"
                       "  mybuf u(.a(a), .y(y));\n"
                       "  always @(y) if ($time > 20)\n"
                       "    $display(\"t=%0t y=%b\", $time, y);\n"
                       "  initial begin\n"
                       "    a = 0;\n"
                       "    #50 a = 1;\n"
                       "    #50 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=55 y=1\nt=105 y=0\n");
}

std::string IfnoneBesideEdgePath(std::string_view c_value) {
  std::string source =
      "module m(input c, input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    if (c) (posedge a => y) = 13;\n"
      "    ifnone (a => y) = 21;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic c, a;\n"
      "  wire y;\n"
      "  m u(.c(c), .a(a), .y(y));\n"
      "  always @(y) if ($time > 30)\n"
      "    $display(\"t=%0t y=%b\", $time, y);\n"
      "  initial begin\n"
      "    c = ";
  source += c_value;
  source +=
      "; a = 0;\n"
      "    #50 a = 1;\n"
      "  end\n"
      "endmodule\n";
  return source;
}

TEST(IfnoneConditionSim, TrueEdgePathConditionOutranksTheIfnonePath) {
  SimFixture f;
  EXPECT_EQ(RunCapture(IfnoneBesideEdgePath("1"), f), "t=63 y=1\n");
}

TEST(IfnoneConditionSim, IfnonePathGovernsWhenTheEdgePathConditionIsFalse) {
  SimFixture f;
  EXPECT_EQ(RunCapture(IfnoneBesideEdgePath("0"), f), "t=71 y=1\n");
}

}  // namespace
