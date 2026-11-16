#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

std::string InTop(const std::string& units, const std::string& items) {
  return units +
         "module top;\n"
         "  logic clk = 0;\n"
         "  always #5 clk = ~clk;\n" +
         items +
         "  initial #42 $finish;\n"
         "endmodule\n";
}

TEST(UnsatisfiableAssumption, FailsOnceAtEachTickAndTheRunGoesOn) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(InTop("checker chk(logic clk);\n"
                          "  rand bit r;\n"
                          "  int fail = 0;\n"
                          "  m1: assume property (@(posedge clk) r && !r) "
                          "else fail++;\n"
                          "endchecker\n",
                          "  bit done = 1'b0;\n"
                          "  chk c(clk);\n"
                          "  initial #41 done = 1'b1;\n"),
                    f, "c.fail"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.fail"), 4u);
  EXPECT_EQ(ValueOf(f, "done"), 1u);
}

TEST(UnsatisfiableAssumption, OnlyItsOwnClockReportsBesideASatisfiedOne) {
  SimFixture f;
  auto run = RunPlaced(
      "checker chk(logic clka, logic clkb);\n"
      "  rand bit r;\n"
      "  rand bit [7:0] s;\n"
      "  int bfail = 0;\n"
      "  m1: assume property (@(posedge clka) r && !r);\n"
      "  m2: assume property (@(posedge clkb) s == 8'd42);\n"
      "  a2: assert property (@(posedge clkb) s == 8'd42) else bfail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clka = 0, clkb = 0;\n"
      "  always #10 clka = ~clka;\n"
      "  initial begin #5; forever #10 clkb = ~clkb; end\n"
      "  chk c(clka, clkb);\n"
      "  initial #72 $finish;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(run.lines,
            "[10] ERROR top.c.m1: Assertion failed.\n"
            "[30] ERROR top.c.m1: Assertion failed.\n"
            "[50] ERROR top.c.m1: Assertion failed.\n"
            "[70] ERROR top.c.m1: Assertion failed.\n");
  EXPECT_EQ(ValueOf(f, "c.bfail"), 0u);
}

TEST(UnsatisfiableAssumption, AConflictInTheConsequentFailsWhereItIsChecked) {
  auto run = RunPlaced(
      InTop("checker chk(logic clk);\n"
            "  rand bit r;\n"
            "  m1: assume property (@(posedge clk) 1'b1 |=> (r && !r));\n"
            "endchecker\n",
            "  chk c(clk);\n"));
  EXPECT_EQ(run.lines,
            "[15] ERROR top.c.m1: Assertion failed.\n"
            "[25] ERROR top.c.m1: Assertion failed.\n"
            "[35] ERROR top.c.m1: Assertion failed.\n");
}

TEST(UnsatisfiableAssumption, DisableIffHoldsBackItsFailures) {
  auto run = RunPlaced(
      InTop("checker chk(logic clk, logic d);\n"
            "  rand bit r;\n"
            "  m1: assume property (@(posedge clk) disable iff (d) r && !r);\n"
            "endchecker\n",
            "  logic d = 1;\n"
            "  initial #22 d = 0;\n"
            "  chk c(clk, d);\n"));
  EXPECT_EQ(run.lines,
            "[25] ERROR top.c.m1: Assertion failed.\n"
            "[35] ERROR top.c.m1: Assertion failed.\n");
}

TEST(UnsatisfiableAssumption, AProceduralAssumptionFailsOnlyWhereEnabled) {
  auto run =
      RunPlaced(InTop("checker chk(logic clk, logic en);\n"
                      "  rand bit r;\n"
                      "  always_ff @(posedge clk)\n"
                      "    if (en) m1: assume property (r && !r);\n"
                      "endchecker\n",
                      "  logic en = 0;\n"
                      "  initial #22 en = 1;\n"
                      "  chk c(clk, en);\n"));
  EXPECT_EQ(run.lines,
            "[25] ERROR top.c.m1: Assertion failed.\n"
            "[35] ERROR top.c.m1: Assertion failed.\n");
}

TEST(UnsatisfiableAssumption, AChildsFailsUnderItsOwnNameAtItsClock) {
  auto run =
      RunPlaced(InTop("checker kid(logic clk, bit x);\n"
                      "  m1: assume property (@(posedge clk) x && !x);\n"
                      "endchecker\n"
                      "checker chk(logic clk);\n"
                      "  rand bit q;\n"
                      "  kid k(clk, q);\n"
                      "endchecker\n",
                      "  chk c(clk);\n"));
  EXPECT_EQ(run.lines,
            PlacedExpected("[5] ERROR top.c.k.m1: Assertion failed.\n"
                           "[15] ERROR top.c.k.m1: Assertion failed.\n"
                           "[25] ERROR top.c.k.m1: Assertion failed.\n"
                           "[35] ERROR top.c.k.m1: Assertion failed.\n",
                           ""));
}

TEST(UnsatisfiableAssumption, AProceduralInstanceFailsAtEachTick) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(InTop("checker chk(logic clk);\n"
                          "  rand bit r;\n"
                          "  int fail = 0;\n"
                          "  m1: assume property (@(posedge clk) r && !r) "
                          "else fail++;\n"
                          "endchecker\n",
                          "  always @(posedge clk) chk c(clk);\n"),
                    f, "c.fail"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.fail"), 4u);
}

TEST(UnsatisfiableAssumption, TheElseActionRunsAfterTheActiveRegion) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(InTop("checker chk(logic clk, output int o);\n"
                          "  rand bit r;\n"
                          "  int fail = 0;\n"
                          "  m1: assume property (@(posedge clk) r && !r) "
                          "else fail++;\n"
                          "  assign o = fail;\n"
                          "endchecker\n",
                          "  int o, now_v, later_v;\n"
                          "  chk c(clk, o);\n"
                          "  always @(posedge clk) begin\n"
                          "    now_v = o;\n"
                          "    #1 later_v = o;\n"
                          "  end\n"),
                    f, "now_v"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "now_v"), 3u);
  EXPECT_EQ(ValueOf(f, "later_v"), 4u);
}

}  // namespace
