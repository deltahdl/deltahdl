#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_expect_runs.h"

using namespace delta;

namespace {

TEST(ExpectStatementRun, BlocksUntilTheSequenceMatchesOrFails) {
  SimFixture f;
  std::string out =
      RunCapture(ExpectDesign("    expect (@(posedge clk) a ##1 b ##1 c)\n"
                              "      $display(\"matched at %0d\", $time);\n"
                              "      else $display(\"failed at %0d\", $time);\n"
                              "    $display(\"after at %0d\", $time);\n"
                              "    expect (@(posedge clk) a ##1 b ##1 c)\n"
                              "      $display(\"matched at %0d\", $time);\n"
                              "      else $display(\"failed at %0d\", $time);\n"
                              "    $display(\"after at %0d\", $time);\n"),
                 f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "matched at 45\nafter at 45\nfailed at 55\nafter at 55\n"
            "$finish at time 210\n");
}

TEST(ExpectStatementRun, OnlyItsOwnProcessWaitsAndAnOpenPropertyKeepsIt) {
  SimFixture f;
  std::string out = RunCapture(
      ExpectDesign("    fork\n"
                   "      repeat (3) @(posedge clk) $display(\"tick at %0d\", "
                   "$time);\n"
                   "    join_none\n"
                   "    expect (@(posedge clk) ##[1:$] data == 1000)\n"
                   "      $display(\"matched at %0d\", $time);\n"
                   "      else $display(\"failed at %0d\", $time);\n"
                   "    $display(\"after at %0d\", $time);\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "tick at 25\ntick at 35\ntick at 45\n$finish at time 210\n");
}

TEST(ExpectStatementRun, AFailureWithoutAnElseClauseReportsAnError) {
  SimFixture f;
  std::string out =
      RunCapture(ExpectDesign("    expect (@(posedge clk) a ##1 b ##1 c) ;\n"
                              "    expect (@(posedge clk) a);\n"
                              "    $display(\"after at %0d\", $time);\n"),
                 f);
  EXPECT_EQ(out, "after at 55\n$finish at time 210\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(ExpectStatementRun, ThePropertyReadsAnAutomaticArgument) {
  SimFixture f;
  std::string out =
      RunCapture(ExpectDesign("    wait_for(9, ok);\n"
                              "    $display(\"ok=%0d at %0d\", ok, $time);\n"
                              "    wait_for(30, ok);\n"
                              "    $display(\"ok=%0d at %0d\", ok, $time);\n"),
                 f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "ok=1 at 95\nok=0 at 205\n$finish at time 210\n");
}

}  // namespace
