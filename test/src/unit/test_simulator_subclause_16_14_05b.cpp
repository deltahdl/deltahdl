#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

// A module around the statements given, as
// test/src/e2e/static_concurrent_assertions.sv is: clk rises at 5, 15, ...,
// 75, tick n at 10n - 5; a is high at ticks 1, 3 and 6, b at 1, 3, 4, 6
// and 7 and c at 2, 5 and 7; the run ends at 80. The clause's rule3 is
// declared as a property and the clause's seq3 as a sequence.
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

// §16.14.5: the clause's a1 asserts rule3 from the beginning to the end of
// simulation, an attempt beginning at every tick: the attempts from 1 and 6
// hold at 2 and 7, the attempt from 3 fails at 4 and the five attempts at
// which a is low hold vacuously.
TEST(StaticConcurrentAssertionRun, AnAssertOfANamedPropertyIsAlwaysChecked) {
  SimFixture f;
  RunAndFindVar(
      StaticSource("  a1: assert property (rule3) passes++; else fails++;\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 7u);
  EXPECT_EQ(Count(f, "fails"), 1u);
}

// §16.14.5: assert property (ps) action_block is equivalent to always assert
// property (ps) action_block ;, so the always form attempts at every tick
// as the bare form does and counts the same.
TEST(StaticConcurrentAssertionRun, TheAlwaysFormOfAnAssertIsTheBareForm) {
  SimFixture f;
  RunAndFindVar(StaticSource("  always assert property (rule3)\n"
                             "    passes++; else fails++;;\n"),
                f, "passes");
  EXPECT_EQ(Count(f, "passes"), 7u);
  EXPECT_EQ(Count(f, "fails"), 1u);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

// §16.14.5: the clause's c1 covers seq3 from the beginning to the end of
// simulation, the sequence always monitored for coverage: the attempts
// from 1, 4 and 6 match at 2, 5 and 7.
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

// §16.14.5: cover property (ps) statement_or_null is equivalent to always
// cover property (ps) statement_or_null, so the always form is covered as
// the bare form is, its results named by the module alone, the form
// carrying no label.
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

// §16.14.5: the statement can be used within an interface, again outside
// any procedural context, where it has the same always semantics: the
// interface's assert of its own rule3 over its ports fails at 4 as the
// module's does.
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

// §16.14.5: the module's own declarations are what its statements
// instantiate wherever the statement stands among the items: a cover of the
// module's seq3 after the instance of an interface declaring a rule3 of its
// own reads the module's seq3, and an assert of rule3 in a generate block
// reads the module's rule3, both evaluated from the beginning to the end.
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
