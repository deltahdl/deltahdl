#include <gtest/gtest.h>

#include <cstdint>
#include <sstream>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string CountingDesign(const std::string& units, const std::string& items,
                           const std::string& module_items, int end) {
  return units +
         "checker chk(int b, logic clk);\n"
         "  bit go = 1'b1;\n" +
         items +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  int b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) b = b + 1;\n" +
         module_items + "  initial #" + std::to_string(end) +
         " $finish;\n"
         "endmodule\n";
}

std::string SolvedFromCount(const std::string& items, int end = 42) {
  return CountingDesign(
      "",
      "  rand bit [15:0] v;\n"
      "  m1: assume property (@(posedge clk) v == 16'(b) + 16'd1000);\n" +
          items,
      "  chk c(b, clk);\n", end);
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

uint64_t RunAndRead(const std::string& src, std::string_view name) {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(SolvedFreeVariableWakeup, DISABLED_AlwaysCombFollowsEachUpdate) {
  EXPECT_EQ(RunAndRead(SolvedFromCount("  bit [15:0] cp;\n"
                                       "  always_comb cp = v;\n"),
                       "c.cp"),
            1003u);
}

TEST(SolvedFreeVariableWakeup, DISABLED_AlwaysLatchFollowsEachUpdate) {
  EXPECT_EQ(RunAndRead(SolvedFromCount("  bit [15:0] cl;\n"
                                       "  always_latch if (go) cl = v;\n"),
                       "c.cl"),
            1003u);
}

TEST(SolvedFreeVariableWakeup, DISABLED_ContinuousAssignmentFollowsEachUpdate) {
  EXPECT_EQ(RunAndRead(SolvedFromCount("  bit [15:0] ca;\n"
                                       "  assign ca = v;\n"),
                       "c.ca"),
            1003u);
}

TEST(SolvedFreeVariableWakeup, DISABLED_AnOutputPortFollowsAndWakesTheModule) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          "checker chk(int b, logic clk, output bit [15:0] o,\n"
          "            output bit [15:0] o2);\n"
          "  rand bit [15:0] v;\n"
          "  m1: assume property (@(posedge clk) v == 16'(b) + 16'd1000);\n"
          "  assign o = v;\n"
          "  always_ff @(posedge clk) o2 <= v;\n"
          "endchecker\n"
          "module top;\n"
          "  logic clk = 0;\n"
          "  int b = 0, n = 0;\n"
          "  bit [15:0] o, o2;\n"
          "  always #5 clk = ~clk;\n"
          "  always @(posedge clk) b = b + 1;\n"
          "  chk c(b, clk, o, o2);\n"
          "  always @(o) n++;\n"
          "  initial #42 $finish;\n"
          "endmodule\n",
          f, "o"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "o"), 1003u);
  EXPECT_EQ(ValueOf(f, "o2"), 1003u);
  EXPECT_GE(ValueOf(f, "n"), 4u);
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_AnyChangeEventControlFiresOnlyOnAChange) {
  EXPECT_EQ(RunAndRead(CountingDesign("",
                                      "  rand bit [15:0] v = 16'd1000;\n"
                                      "  m1: assume property (@(posedge clk)\n"
                                      "    v == 16'(b / 2) + 16'd1000);\n"
                                      "  int n = 0;\n"
                                      "  always_ff @(v) n <= n + 1;\n",
                                      "  chk c(b, clk);\n", 62),
                       "c.n"),
            2u);
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_EdgeEventControlsFireOnTheirTransitions) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(CountingDesign("",
                                   "  rand bit v = 1'b0;\n"
                                   "  m1: assume property (@(posedge clk) "
                                   "v == b[0]);\n"
                                   "  int pos = 0, neg = 0;\n"
                                   "  always_ff @(posedge v) pos <= pos + 1;\n"
                                   "  always_ff @(negedge v) neg <= neg + 1;\n",
                                   "  chk c(b, clk);\n", 62),
                    f, "c.pos"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.pos"), 3u);
  EXPECT_EQ(ValueOf(f, "c.neg"), 2u);
}

TEST(SolvedFreeVariableWakeup, DISABLED_AChildCheckerWakesThroughItsFormal) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(CountingDesign("checker kid(bit x);\n"
                                   "  int pos = 0;\n"
                                   "  bit cp;\n"
                                   "  always_ff @(posedge x) pos <= pos + 1;\n"
                                   "  always_comb cp = x;\n"
                                   "endchecker\n",
                                   "  rand bit v = 1'b0;\n"
                                   "  m1: assume property (@(posedge clk) "
                                   "v == b[0]);\n"
                                   "  kid k(v);\n",
                                   "  chk c(b, clk);\n", 62),
                    f, "c.k.pos"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.k.pos"), 3u);
  EXPECT_EQ(ValueOf(f, "c.k.cp"), 1u);
}

std::string ChangesCountedAtEachTick(const std::string& watched) {
  return "  int changes = 0;\n"
         "  bit [15:0] last;\n"
         "  always_ff @(posedge clk) begin\n"
         "    if (" +
         watched +
         " != last) changes <= changes + 1;\n"
         "    last <= " +
         watched +
         ";\n"
         "  end\n";
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_ImplicitlyClockedUpdatesWakeTheirReaders) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                CountingDesign("",
                               "  rand bit [15:0] v;\n"
                               "  m1: assume property (@(posedge clk) clk);\n"
                               "  bit [15:0] cp, ca;\n"
                               "  int n = 0;\n"
                               "  always_comb cp = v;\n"
                               "  assign ca = v;\n"
                               "  always_ff @(v) n <= n + 1;\n" +
                                   ChangesCountedAtEachTick("cp"),
                               "  chk c(b, clk);\n", 202),
                f, "c.changes"),
            nullptr);
  EXPECT_GT(ValueOf(f, "c.changes"), 10u);
  EXPECT_GT(ValueOf(f, "c.n"), 10u);
  EXPECT_EQ(ValueOf(f, "c.ca"), ValueOf(f, "c.v"));
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_AnUnconstrainedVariableWakesItsReaders) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(CountingDesign("",
                                   "  rand bit [15:0] x, y;\n"
                                   "  m1: assume property (@(posedge clk) "
                                   "x == 16'd3);\n"
                                   "  bit [15:0] cy;\n"
                                   "  always_comb cy = y;\n" +
                                       ChangesCountedAtEachTick("cy"),
                                   "  chk c(b, clk);\n", 202),
                    f, "c.changes"),
      nullptr);
  EXPECT_GT(ValueOf(f, "c.changes"), 10u);
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_StructureAndEnumVariablesWakeTheirReaders) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          CountingDesign(
              "",
              "  typedef struct packed { bit [7:0] p; bit [7:0] q; } st_t;\n"
              "  typedef enum bit [1:0] { A, B, C, D } e_t;\n"
              "  rand st_t s;\n"
              "  rand e_t e;\n"
              "  m1: assume property (@(posedge clk)\n"
              "    s == {8'(b) + 8'd100, 8'd7} && e == e_t'(b[1:0]));\n"
              "  bit [15:0] cs;\n"
              "  bit [1:0] ce;\n"
              "  assign cs = s;\n"
              "  assign ce = e;\n",
              "  chk c(b, clk);\n", 42),
          f, "c.cs"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.cs"), (103u << 8) | 7u);
  EXPECT_EQ(ValueOf(f, "c.ce"), 3u);
}

TEST(SolvedFreeVariableWakeup,
     DISABLED_EveryInstantiationPlaceWakesTheReaders) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                CountingDesign("interface ifc(input int b, input logic clk);\n"
                               "  chk c(b, clk);\n"
                               "endinterface\n"
                               "program pr(input int b, input logic clk);\n"
                               "  chk c(b, clk);\n"
                               "endprogram\n"
                               "checker outer(int b, logic clk);\n"
                               "  chk c(b, clk);\n"
                               "endchecker\n",
                               "  rand bit [15:0] v;\n"
                               "  m1: assume property (@(posedge clk) "
                               "v == 16'(b) + 16'd1000);\n"
                               "  bit [15:0] ca;\n"
                               "  assign ca = v;\n",
                               "  chk c(b, clk);\n"
                               "  ifc i(b, clk);\n"
                               "  pr p(b, clk);\n"
                               "  outer o(b, clk);\n",
                               42),
                f, "c.ca"),
            nullptr);
  for (std::string_view scope : {"c", "i.c", "p.c", "o.c"}) {
    SCOPED_TRACE(scope);
    EXPECT_EQ(ValueOf(f, std::string(scope) + ".ca"), 1003u);
  }
}

TEST(SolvedFreeVariableWakeup, ASecondClockEventInTheStepSolvesAgain) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar("checker chk(logic clk1);\n"
                    "  rand bit v;\n"
                    "  bit clk2;\n"
                    "  assign clk2 = clk1;\n"
                    "  int ones = 0, zeros = 0, f1 = 0, f2 = 0;\n"
                    "  m1: assume property (@(posedge clk1) v == 1'b0);\n"
                    "  m2: assume property (@(posedge clk2) v == 1'b1);\n"
                    "  a1: assert property (@(posedge clk1) v == 1'b0) "
                    "else f1++;\n"
                    "  a2: assert property (@(posedge clk2) v == 1'b1) "
                    "else f2++;\n"
                    "  always_ff @(negedge clk1)\n"
                    "    if (v) ones <= ones + 1; else zeros <= zeros + 1;\n"
                    "endchecker\n"
                    "module top;\n"
                    "  logic clk1 = 0;\n"
                    "  always #5 clk1 = ~clk1;\n"
                    "  chk c(clk1);\n"
                    "  initial #95 $finish;\n"
                    "endmodule\n",
                    f, "c.ones"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.ones"), 9u);
  EXPECT_EQ(ValueOf(f, "c.zeros"), 0u);
  EXPECT_EQ(ValueOf(f, "c.f1"), 0u);
  EXPECT_EQ(ValueOf(f, "c.f2"), 0u);
}

TEST(SolvedFreeVariableWakeup, AnUpdatedValueHoldsToTheEndOfItsTimeStep) {
  SimFixture f;
  std::string out =
      RunCapture(SolvedFromCount("  always_ff @(posedge clk) begin\n"
                                 "    $display(\"D %0t %0d\", $time, v);\n"
                                 "    $strobe(\"S %0t %0d\", $time, v);\n"
                                 "  end\n"),
                 f);
  for (int tick = 0; tick < 4; ++tick) {
    std::ostringstream at;
    at << (5 + 10 * tick) << " " << (1000 + tick);
    SCOPED_TRACE(at.str());
    EXPECT_NE(out.find("D " + at.str() + "\n"), std::string::npos) << out;
    EXPECT_NE(out.find("S " + at.str() + "\n"), std::string::npos) << out;
  }
}

TEST(SolvedFreeVariableWakeup, AnExplicitlyClockedValueHoldsBetweenEvents) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(SolvedFromCount("  bit [15:0] h;\n"
                                          "  int good = 0, bad = 0;\n"
                                          "  always_ff @(posedge clk) h <= v;\n"
                                          "  always_ff @(negedge clk)\n"
                                          "    if (v == h) good <= good + 1;\n"
                                          "    else bad <= bad + 1;\n",
                                          102),
                          f, "c.good"),
            nullptr);
  EXPECT_EQ(ValueOf(f, "c.good"), 10u);
  EXPECT_EQ(ValueOf(f, "c.bad"), 0u);
}

}  // namespace
