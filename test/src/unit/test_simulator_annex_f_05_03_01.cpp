#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr const char* kThreeTicks =
    "  initial begin\n"
    "    #10 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 1;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 0;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "  end\n";

std::string Design(const std::string& statement) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n" +
         statement + kThreeTicks + "endmodule\n";
}

TEST(NeutralSatisfactionAtARun, AnAssumeIsJudgedAsTheAssertWithItsBody) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      Design("  assume property (@(posedge clk) a) hits = hits + 1;\n"
             "  else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

TEST(NeutralSatisfactionAtARun, AnAssumeWithoutActionsReportsAsAnAssert) {
  SimFixture f;
  auto* design =
      ElaborateSrc(Design("  assume property (@(posedge clk) a);\n"), f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(NeutralSatisfactionAtARun, ACoverPassesAtTheTicksItsBodyHolds) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      Design("  cover property (@(posedge clk) a) hits = hits + 1;\n"), f,
      "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(NeutralSatisfactionAtARun, ACoverReportsNothingWhereItsBodyDoesNotHold) {
  SimFixture f;
  auto* design =
      ElaborateSrc(Design("  cover property (@(posedge clk) a);\n"), f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "");
}

TEST(NeutralSatisfactionAtARun, ACoverIsJudgedOnTheSampledWord) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  int hits = 0;\n"
      "  cover property (@(posedge clk) a) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
}

}  // namespace
