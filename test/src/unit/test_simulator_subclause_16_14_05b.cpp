#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

std::string StaticSource(const std::string& statements) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c;\n"
         "  int passes = 0, fails = 0, covered = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 3, 6};\n"
         "  assign b = tick inside {1, 3, 4, 6, 7};\n"
         "  assign c = tick inside {2, 5, 7};\n"
         "  property rule3;\n"
         "    @(posedge clk) a |-> b ##1 c;\n"
         "  endproperty\n"
         "  sequence seq3;\n"
         "    @(posedge clk) b ##1 c;\n"
         "  endsequence\n" +
         statements +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

uint64_t Count(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(StaticConcurrentAssertionRun, AnAssertOfANamedPropertyIsAlwaysChecked) {
  SimFixture f;
  RunAndFindVar(
      StaticSource("  a1: assert property (rule3) passes++; else fails++;\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 7u);
  EXPECT_EQ(Count(f, "fails"), 1u);
}

TEST(StaticConcurrentAssertionRun, TheAlwaysFormOfAnAssertIsTheBareForm) {
  SimFixture f;
  RunAndFindVar(StaticSource("  always assert property (rule3)\n"
                             "    passes++; else fails++;;\n"),
                f, "passes");
  EXPECT_EQ(Count(f, "passes"), 7u);
  EXPECT_EQ(Count(f, "fails"), 1u);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(StaticConcurrentAssertionRun, ACoverOfANamedSequenceIsAlwaysMonitored) {
  SimFixture f;
  RunAndFindVar(StaticSource("  c1: cover property (seq3) covered++;\n"), f,
                "covered");
  EXPECT_EQ(Count(f, "covered"), 3u);
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].scope, "t.c1");
  EXPECT_EQ(results[0].attempted, 8u);
  EXPECT_EQ(results[0].succeeded, 3u);
}

TEST(StaticConcurrentAssertionRun, TheAlwaysFormOfACoverIsTheBareForm) {
  SimFixture f;
  RunAndFindVar(StaticSource("  always cover property (seq3) covered++;\n"), f,
                "covered");
  EXPECT_EQ(Count(f, "covered"), 3u);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].scope, "t");
  EXPECT_EQ(results[0].attempted, 8u);
  EXPECT_EQ(results[0].succeeded, 3u);
}

TEST(StaticConcurrentAssertionRun, AnAssertInAnInterfaceIsAlwaysChecked) {
  SimFixture f;
  std::string out = RunCapture(
      "interface bus_if(input logic clk, input logic a, input logic b,\n"
      "                 input logic c);\n"
      "  property rule3;\n"
      "    @(posedge clk) a |-> b ##1 c;\n"
      "  endproperty\n"
      "  if_a1: assert property (rule3)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "endinterface\n" +
          StaticSource("  bus_if bus(clk, a, b, c);\n"),
      f);
  EXPECT_EQ(out, "t.bus.if_a1 failed at 35\n$finish at time 80\n");
}

TEST(StaticConcurrentAssertionRun,
     AStatementAfterAnInstanceOrInAGenerateReadsItsOwnModulesDeclarations) {
  SimFixture f;
  RunAndFindVar(
      "interface bus_if(input logic clk, input logic a, input logic b,\n"
      "                 input logic c);\n"
      "  property rule3;\n"
      "    @(posedge clk) a |-> b ##1 c;\n"
      "  endproperty\n"
      "  if_a1: assert property (rule3);\n"
      "endinterface\n" +
          StaticSource("  bus_if bus(clk, a, b, c);\n"
                       "  c1: cover property (seq3) covered++;\n"
                       "  if (1) begin : gen\n"
                       "    g1: assert property (rule3) passes++;\n"
                       "    else fails++;\n"
                       "  end\n"),
      f, "covered");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "covered"), 3u);
  EXPECT_EQ(Count(f, "passes"), 7u);
  EXPECT_EQ(Count(f, "fails"), 1u);
}

}  // namespace
