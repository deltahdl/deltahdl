#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

std::string ProceduralSource(const std::string& procedures) {
  return "module t;\n"
         "  logic mclk = 0, scanclk = 0, fastclk = 0, clock = 0;\n"
         "  logic reset = 0;\n"
         "  logic d1 = 0, d = 1, q = 0;\n"
         "  logic d2 = 1, q2 = 0;\n"
         "  int cnt = 0;\n"
         "  int passes = 0, fails = 0, hits = 0;\n"
         "  always #10 mclk = ~mclk;\n"
         "  always #20 scanclk = ~scanclk;\n"
         "  always #5 fastclk = ~fastclk;\n"
         "  always #15 clock = ~clock;\n"
         "  property r1;\n"
         "    q != d;\n"
         "  endproperty\n"
         "  property r2;\n"
         "    q2 != d2;\n"
         "  endproperty\n" +
         procedures +
         "  initial begin\n"
         "    #25 d1 = 1;\n"
         "    #15 reset = 1;\n"
         "    #10 reset = 0;\n"
         "    #15 d1 = 0;\n"
         "    #55 $finish;\n"
         "  end\n"
         "endmodule\n";
}

uint64_t Count(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(ProceduralConcurrentAssertionRun, AnInferredClockEvaluatesAtItsOwnTick) {
  SimFixture f;
  RunAndFindVar(ProceduralSource("  always @(posedge mclk) begin\n"
                                 "    q <= d1;\n"
                                 "    r1_p1: assert property (r1) passes++;\n"
                                 "    else fails++;\n"
                                 "  end\n"),
                f, "passes");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "passes"), 4u);
  EXPECT_EQ(Count(f, "fails"), 2u);
}

TEST(ProceduralConcurrentAssertionRun,
     ASlowerOwnClockEvaluatesEveryMaturedInstanceAtItsNextTick) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    r1_p2: assert property (@(posedge scanclk) r1)\n"
                       "      $display(\"passed at %0d\", $time);\n"
                       "    else $display(\"failed at %0d\", $time);\n"
                       "  end\n"),
      f);
  EXPECT_EQ(out,
            "passed at 20\nfailed at 60\nfailed at 60\npassed at 100\n"
            "passed at 100\n$finish at time 120\n");
}

TEST(ProceduralConcurrentAssertionRun,
     AFasterOwnClockEvaluatesOnlyAtTheTicksAfterAnInstanceWasQueued) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    r1_p3: assert property (@(posedge fastclk) r1)\n"
                       "      $display(\"passed at %0d\", $time);\n"
                       "    else $display(\"failed at %0d\", $time);\n"
                       "  end\n"),
      f);
  EXPECT_EQ(out,
            "passed at 15\nfailed at 35\nfailed at 55\npassed at 75\n"
            "passed at 95\npassed at 115\n$finish at time 120\n");
}

TEST(ProceduralConcurrentAssertionRun, EachReachInAStepQueuesAnInstance) {
  SimFixture f;
  RunAndFindVar(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    for (int i = 0; i < 3; i++)\n"
                       "      loop_p: assert property (r1) passes++;\n"
                       "      else fails++;\n"
                       "  end\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 12u);
  EXPECT_EQ(Count(f, "fails"), 6u);
}

TEST(ProceduralConcurrentAssertionRun,
     AnInstanceWhoseClockDidNotOccurWaitsForItsNextTick) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource(
          "  always_ff @(posedge clock iff reset == 0 or posedge reset)\n"
          "  begin\n"
          "    cnt <= reset ? 0 : cnt + 1;\n"
          "    q2 <= d2;\n"
          "    r2_p: assert property (r2) $display(\"passed at %0d\", $time);\n"
          "    else $display(\"failed at %0d\", $time);\n"
          "  end\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "passed at 15\nfailed at 75\nfailed at 75\nfailed at 105\n"
            "$finish at time 120\n");
}

TEST(ProceduralConcurrentAssertionRun,
     TheDefaultClockingClocksWhatNoContextDoes) {
  SimFixture f;
  RunAndFindVar(ProceduralSource(
                    "  default clocking dc @(posedge scanclk); endclocking\n"
                    "  initial begin\n"
                    "    #12;\n"
                    "    r4_p: assert property (r1) passes++; else fails++;\n"
                    "  end\n"),
                f, "passes");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "passes"), 1u);
  EXPECT_EQ(Count(f, "fails"), 0u);
}

TEST(ProceduralConcurrentAssertionRun,
     ACoverAndATemporalPropertyAreQueuedAndEvaluated) {
  SimFixture f;
  RunAndFindVar(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    c_p: cover property (q == d1) hits++;\n"
                       "    t_p: assert property (d1 |=> q) passes++;\n"
                       "    else fails++;\n"
                       "  end\n"),
      f, "hits");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "hits"), 4u);
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].scope, "t.c_p");
  EXPECT_EQ(results[0].attempted, 6u);
  EXPECT_EQ(results[0].succeeded, 4u);
  EXPECT_EQ(Count(f, "passes"), 6u);
  EXPECT_EQ(Count(f, "fails"), 0u);
}

TEST(ProceduralConcurrentAssertionRun,
     AnAssertionNoClockReachesIsReportedAndItsProcedureRunsOn) {
  SimFixture f;
  RunAndFindVar(
      ProceduralSource("  always begin\n"
                       "    #7 cnt = cnt + 1;\n"
                       "    a_p: assert property (r1) passes++; else fails++;\n"
                       "  end\n"),
      f, "cnt");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "no clock is inferred for the procedural concurrent assertion", 20,
      "16.14.6"));
  EXPECT_EQ(Count(f, "cnt"), 17u);
}

}  // namespace
