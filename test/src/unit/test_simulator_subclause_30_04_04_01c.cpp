#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string ConditionRun(const std::string& condition,
                         const std::string& setup) {
  SimFixture f;
  return RunCapture(
      "module dut(input a, output y);\n"
      "  logic sa, armed;\n"
      "  logic [1:0] c;\n"
      "  logic e;\n"
      "  assign a = sa;\n"
      "  assign y = a;\n"
      "  specify\n"
      "    if (" +
          condition +
          ") (a => y) = 13;\n"
          "  endspecify\n"
          "  always @(y) if (armed) $display(\"edge %b at %0d\", y, $time);\n"
          "  initial begin\n"
          "    armed = 0;\n"
          "    sa = 0;\n"
          "    " +
          setup +
          "\n"
          "    #40 armed = 1;\n"
          "    #10 sa = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

constexpr const char* kPathTaken = "edge 1 at 63\n";
constexpr const char* kPathSkipped = "edge 1 at 50\n";

TEST(StateDependentPathConditionRun, TrueConditionTakesThePathDelay) {
  EXPECT_EQ(ConditionRun("c[0]", "c = 2'b01;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, FalseConditionSkipsThePathDelay) {
  EXPECT_EQ(ConditionRun("c[0]", "c = 2'b00;"), kPathSkipped);
}

TEST(StateDependentPathConditionRun, UnknownConditionTakesThePathDelay) {
  EXPECT_EQ(ConditionRun("c[0]", "c = 2'bxx;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, HighImpedanceConditionTakesThePathDelay) {
  EXPECT_EQ(ConditionRun("c[0]", "c = 2'bzz;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, UnknownResultOfAnOperatorTakesThePath) {
  EXPECT_EQ(ConditionRun("c[1] ^ e", "c = 2'b00; e = 1'bx;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, KnownFalseResultOfAnOperatorSkipsThePath) {
  EXPECT_EQ(ConditionRun("c[1] ^ e", "c = 2'b00; e = 1'b0;"), kPathSkipped);
}

TEST(StateDependentPathConditionRun, MultiBitConditionWithLsbZeroSkipsThePath) {
  EXPECT_EQ(ConditionRun("c", "c = 2'b10;"), kPathSkipped);
}

TEST(StateDependentPathConditionRun, MultiBitConditionWithLsbOneTakesThePath) {
  EXPECT_EQ(ConditionRun("c", "c = 2'b01;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, UnknownUpperBitLeavesLsbZeroSkipping) {
  EXPECT_EQ(ConditionRun("c", "c = 2'bx0;"), kPathSkipped);
}

TEST(StateDependentPathConditionRun, UnknownLsbOfAMultiBitConditionTakesPath) {
  EXPECT_EQ(ConditionRun("c", "c = 2'b0x;"), kPathTaken);
}

TEST(StateDependentPathConditionRun,
     HighImpedanceLsbOfAMultiBitConditionTakes) {
  EXPECT_EQ(ConditionRun("c", "c = 2'b0z;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, ConcatenationResultIsDecidedByItsLsb) {
  EXPECT_EQ(ConditionRun("{c[0], c[1]}", "c = 2'b10;"), kPathTaken);
}

TEST(StateDependentPathConditionRun, ConcatenationWithLsbZeroSkipsThePath) {
  EXPECT_EQ(ConditionRun("{c[0], c[1]}", "c = 2'b01;"), kPathSkipped);
}

}  // namespace
