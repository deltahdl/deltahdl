#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string WithInputLowAtFifteen(const std::string& checker,
                                  const std::string& instance) {
  return checker +
         "module top;\n"
         "  logic clk = 0, a = 1;\n"
         "  always #5 clk = ~clk;\n" +
         instance +
         "  initial begin #12 a = 0; #10 a = 1; #20 $finish; end\n"
         "endmodule\n";
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

void ExpectCounts(SimFixture& f, std::string_view scope, uint64_t pass,
                  uint64_t fail) {
  EXPECT_EQ(ValueOf(f, std::string(scope) + ".pass"), pass);
  EXPECT_EQ(ValueOf(f, std::string(scope) + ".fail"), fail);
}

constexpr std::string_view kCountingChecker =
    "checker chk(logic clk, logic a);\n"
    "  int pass = 0, fail = 0;\n"
    "  m1: assume property (@(posedge clk) a) pass++; else fail++;\n"
    "endchecker\n";

TEST(CheckerAssumeViolation, AnAssumptionOverAnInputFailsWhereItIsLow) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(WithInputLowAtFifteen(std::string(kCountingChecker),
                                                "  chk c(clk, a);\n"),
                          f, "c.pass"),
            nullptr);
  ExpectCounts(f, "c", 3, 1);
}

TEST(CheckerAssumeViolation, AnAssumptionWithoutActionsReportsTheDefaultError) {
  auto run = RunPlaced(
      WithInputLowAtFifteen("checker chk(logic clk, logic a);\n"
                            "  m1: assume property (@(posedge clk) a);\n"
                            "endchecker\n",
                            "  chk c(clk, a);\n"));
  EXPECT_EQ(run.lines, "[15] ERROR top.c.m1: Assertion failed.\n");
}

TEST(CheckerAssumeViolation,
     AnAssumptionOverAPropertyFormalFailsWithItsActual) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen(
                        "checker chk(property p, logic clk);\n"
                        "  int pass = 0, fail = 0;\n"
                        "  m1: assume property (@(posedge clk) p) pass++; "
                        "else fail++;\n"
                        "endchecker\n",
                        "  logic b = 1;\n"
                        "  chk c(b |-> a, clk);\n"),
                    f, "c.pass"),
      nullptr);
  ExpectCounts(f, "c", 3, 1);
}

TEST(CheckerAssumeViolation, AnAssumptionOutsideTheAssumeSetByConstCastFails) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen(std::string(kCountingChecker),
                                          "  chk c(clk, const'(1'b0));\n"),
                    f, "c.pass"),
      nullptr);
  ExpectCounts(f, "c", 0, 4);
}

TEST(CheckerAssumeViolation,
     AnAssumptionOutsideTheAssumeSetByAnAutomaticActualFails) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen(std::string(kCountingChecker),
                                          "  always @(posedge clk) begin\n"
                                          "    automatic logic w = 1'b0;\n"
                                          "    chk c(clk, w);\n"
                                          "  end\n"),
                    f, "c.pass"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.pass"), 0u);
  EXPECT_GT(ValueOf(f, "c.fail"), 0u);
}

TEST(CheckerAssumeViolation,
     AnAssumptionOverNonFreeAndInactiveVariablesFailsWhereFalse) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen(
                        "checker chk(logic clk, logic a);\n"
                        "  bit t = 1'b0;\n"
                        "  rand bit g = 1'b0;\n"
                        "  int pass = 0, fail = 0, gpass = 0, gfail = 0;\n"
                        "  always_ff @(posedge clk) t <= !t;\n"
                        "  always_ff @(posedge clk) g <= !g;\n"
                        "  m1: assume property (@(posedge clk) t) pass++; "
                        "else fail++;\n"
                        "  m2: assume property (@(posedge clk) g) gpass++; "
                        "else gfail++;\n"
                        "endchecker\n",
                        "  chk c(clk, a);\n"),
                    f, "c.pass"),
      nullptr);
  ExpectCounts(f, "c", 2, 2);
  EXPECT_EQ(ValueOf(f, "c.gpass"), 2u);
  EXPECT_EQ(ValueOf(f, "c.gfail"), 2u);
}

TEST(CheckerAssumeViolation, ASatisfiedAssumptionNeverFails) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(WithInputLowAtFifteen(
                              "checker chk(logic clk, logic a);\n"
                              "  rand bit r;\n"
                              "  int pass = 0, fail = 0;\n"
                              "  m1: assume property (@(posedge clk) r) "
                              "pass++; else fail++;\n"
                              "endchecker\n",
                              "  chk c(clk, a);\n"),
                          f, "c.pass"),
            nullptr);
  ExpectCounts(f, "c", 4, 0);
}

TEST(CheckerAssumeViolation, ContradictingAssumptionsFailOncePerTick) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(WithInputLowAtFifteen(
                              "checker chk(logic clk, logic a, logic b);\n"
                              "  rand bit q;\n"
                              "  int pass = 0, fail = 0;\n"
                              "  m1: assume property (@(posedge clk) q == a) "
                              "pass++; else fail++;\n"
                              "  m2: assume property (@(posedge clk) q != b) "
                              "pass++; else fail++;\n"
                              "endchecker\n",
                              "  logic one = 1'b1;\n"
                              "  chk c(clk, one, one);\n"),
                          f, "c.pass"),
            nullptr);
  ExpectCounts(f, "c", 4, 4);
}

TEST(CheckerAssumeViolation, ADeadEndFailsSixTicksAfterItsChoice) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(
          "checker chk(logic clk);\n"
          "  rand bit x;\n"
          "  int ones = 0, fail = 0;\n"
          "  u1: assume property (@(posedge clk) x |=> ##5 1'b0) else fail++;\n"
          "  always_ff @(posedge clk) if (x && $time <= 135) ones <= ones + "
          "1;\n"
          "endchecker\n"
          "module top;\n"
          "  logic clk = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  chk c(clk);\n"
          "  initial #200 $finish;\n"
          "endmodule\n",
          f, "c.fail"),
      nullptr);
  EXPECT_EQ(ValueOf(f, "c.fail"), ValueOf(f, "c.ones"));
}

TEST(CheckerAssumeViolation, AChildsAssumptionFailsUnderItsOwnName) {
  auto run = RunPlaced(
      WithInputLowAtFifteen("checker kid(logic clk, logic x);\n"
                            "  m1: assume property (@(posedge clk) x);\n"
                            "endchecker\n"
                            "checker chk(logic clk, logic a);\n"
                            "  kid k(clk, a);\n"
                            "endchecker\n",
                            "  chk c(clk, a);\n"));
  EXPECT_EQ(run.lines, "[15] ERROR top.c.k.m1: Assertion failed.\n");
}

TEST(CheckerAssumeViolation,
     AssumptionsInGenerateBlocksFailOnTheirOwnOperands) {
  SimFixture f;
  ASSERT_NE(RunAndFindVar(
                WithInputLowAtFifteen(
                    "checker chk(logic clk, logic [1:0] v, logic a);\n"
                    "  int fi = 0, fc = 0;\n"
                    "  if (1) begin : gi\n"
                    "    m: assume property (@(posedge clk) a) else fi++;\n"
                    "  end\n"
                    "  case (1)\n"
                    "    1: begin : gc\n"
                    "      m: assume property (@(posedge clk) a) else fc++;\n"
                    "    end\n"
                    "  endcase\n"
                    "  for (genvar i = 0; i < 2; i++) begin : gf\n"
                    "    int fl = 0;\n"
                    "    m: assume property (@(posedge clk) v[i]) else fl++;\n"
                    "  end\n"
                    "endchecker\n",
                    "  chk c(clk, 2'b01, a);\n"),
                f, "c.fi"),
            nullptr);
  EXPECT_EQ(ValueOf(f, "c.fi"), 1u);
  EXPECT_EQ(ValueOf(f, "c.fc"), 1u);
  EXPECT_EQ(ValueOf(f, "c.gf[0].fl"), 0u);
  EXPECT_EQ(ValueOf(f, "c.gf[1].fl"), 4u);
}

TEST(CheckerAssumeViolation, AnAssumptionInAlwaysFfTakesItsClock) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen("checker chk(logic clk, logic a);\n"
                                          "  int pass = 0, fail = 0;\n"
                                          "  always_ff @(posedge clk)\n"
                                          "    m1: assume property (a) pass++; "
                                          "else fail++;\n"
                                          "endchecker\n",
                                          "  chk c(clk, a);\n"),
                    f, "c.pass"),
      nullptr);
  ExpectCounts(f, "c", 3, 1);
}

TEST(CheckerAssumeViolation, AnAssumptionInInitialMakesOneAttempt) {
  auto run = RunPlaced(
      "checker chk(logic clk, logic a);\n"
      "  initial m1: assume property (@(posedge clk) a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk, a);\n"
      "  initial #42 $finish;\n"
      "endmodule\n");
  EXPECT_EQ(run.lines, "[5] ERROR top.c.m1: Assertion failed.\n");
}

TEST(CheckerAssumeViolation, ImmediateAssumptionsInAlwaysFfAndInitialFail) {
  auto run = RunPlaced(
      WithInputLowAtFifteen("checker chk(logic clk, logic a, logic z);\n"
                            "  always_ff @(posedge clk) m1: assume (a);\n"
                            "  initial m2: assume (z);\n"
                            "endchecker\n",
                            "  chk c(clk, a, 1'b0);\n"));
  EXPECT_EQ(run.lines,
            "[0] ERROR top.c.m2: Assertion failed.\n"
            "[15] ERROR top.c.m1: Assertion failed.\n");
}

TEST(CheckerAssumeViolation, DeferredAssumptionsFailWhereTheInputSettlesLow) {
  auto run = RunPlaced(
      "checker chk(logic a);\n"
      "  always_comb m1: assume #0 (a);\n"
      "  always_comb m2: assume final (a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic a = 1;\n"
      "  chk c(a);\n"
      "  initial begin\n"
      "    #20 a = 0; a = 1;\n"
      "    #10 a = 0;\n"
      "    #10 a = 1;\n"
      "    #10 $finish;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run.lines,
            "[30] ERROR top.c.m1: Assertion failed.\n"
            "[30] ERROR top.c.m2: Assertion failed.\n");
}

TEST(CheckerAssumeViolation, CheckersInAnInterfaceAndAProgramFailWhereFalse) {
  SimFixture f;
  ASSERT_NE(
      RunAndFindVar(WithInputLowAtFifteen(
                        std::string(kCountingChecker) +
                            "interface ifc(input logic clk, "
                            "input logic a);\n"
                            "  chk c(clk, a);\n"
                            "endinterface\n"
                            "program pr(input logic clk, input logic a);\n"
                            "  chk c(clk, a);\n"
                            "endprogram\n",
                        "  ifc i(clk, a);\n"
                        "  pr p(clk, a);\n"),
                    f, "i.c.pass"),
      nullptr);
  ExpectCounts(f, "i.c", 3, 1);
  ExpectCounts(f, "p.c", 3, 1);
}

}  // namespace
