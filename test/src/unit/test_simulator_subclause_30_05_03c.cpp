#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kModeConditionedPaths =
    "    if (act[4]) (a => y) = (5, 9);\n"
    "    if (act[3]) (a => y) = (4, 8);\n"
    "    if (act[2]) (a => y) = (6, 5);\n"
    "    if (act[1]) (a => y) = (3, 2);\n"
    "    if (act[0]) (a => y) = (7, 7);\n";

constexpr std::string_view kIfnonePaths =
    "    if (act[4]) (a => y) = 13;\n"
    "    ifnone (a => y) = 21;\n";

std::string PathSource(std::string_view setup, std::string_view paths) {
  std::string src = "module dut(input a, output y);\n";
  src += "  logic sa, armed;\n";
  src += "  logic [4:0] act;\n";
  src += "  assign a = sa;\n";
  src += "  assign y = a;\n";
  src += "  specify\n";
  src.append(paths);
  src += "  endspecify\n";
  src += "  always @(y) begin\n";
  src += "    if (armed) $display(\"edge %b at %0d\", y, $time);\n";
  src += "  end\n";
  src += "  initial begin\n";
  src += "    armed = 1'b0;\n";
  src += "    sa = 1'b0;\n";
  src.append(setup);
  src += "    #40 armed = 1'b1;\n";
  src += "    #10 sa = 1'b1;\n";
  src += "  end\n";
  src += "  initial #45 $display(\"at 45 y=%b\", y);\n";
  src += "  initial #80 $display(\"at 80 y=%b\", y);\n";
  src += "endmodule\n";
  return src;
}

TEST(StateDependentPathActivity, FalseConditionsWithholdTheSmallerRiseDelay) {
  SimFixture f;
  std::string out =
      RunCapture(PathSource("    act = 5'b11100;\n", kModeConditionedPaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 54\nat 80 y=1\n");
}

TEST(StateDependentPathActivity, EveryTrueConditionLeavesEveryPathActive) {
  SimFixture f;
  std::string out =
      RunCapture(PathSource("    act = 5'b11111;\n", kModeConditionedPaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 53\nat 80 y=1\n");
}

TEST(StateDependentPathActivity, NoTrueConditionLeavesNoPathActive) {
  SimFixture f;
  std::string out =
      RunCapture(PathSource("    act = 5'b00000;\n", kModeConditionedPaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 50\nat 80 y=1\n");
}

TEST(StateDependentPathActivity, TrueConditionOutranksTheIfnonePath) {
  SimFixture f;
  std::string out =
      RunCapture(PathSource("    act = 5'b10000;\n", kIfnonePaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 63\nat 80 y=1\n");
}

TEST(StateDependentPathActivity, IfnonePathGovernsWhenTheConditionIsFalse) {
  SimFixture f;
  std::string out =
      RunCapture(PathSource("    act = 5'b00000;\n", kIfnonePaths), f);
  EXPECT_EQ(out, "at 45 y=0\nedge 1 at 71\nat 80 y=1\n");
}

}  // namespace
