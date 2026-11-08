#include <gtest/gtest.h>

#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

std::string CoverSource(const std::string& statements) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0, ack = 0, rst = 0;\n"
         "  int hits = 0, reactive_hits = 0, marker = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) marker = $time;\n" +
         statements +
         "  initial begin\n"
         "    #10 req = 1;\n"
         "    #10 req = 0; ack = 1;\n"
         "    #20 ack = 0; req = 1;\n"
         "    #10 req = 0; ack = 1;\n"
         "    #12 rst = 1;\n"
         "    #6 rst = 0;\n"
         "    #2 ack = 0; req = 1;\n"
         "    #10 req = 0;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

const ConcurrentCoverResult* TheRecord(SimFixture& f) {
  const auto& results = f.ctx.ConcurrentCovers().Results();
  return results.size() == 1 ? &results[0] : nullptr;
}

TEST(CoverStatementRun, ACoverPropertysPassStatementRunsOncePerSuccess) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CoverSource(
          "  implied: cover property\n"
          "    (@(posedge clk) disable iff (rst) req |=> ack) hits++;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 7u);
}

TEST(CoverStatementRun, ACoverPropertysResultsCountAttemptsAndSuccesses) {
  SimFixture f;
  RunAndFindVar(
      CoverSource(
          "  implied: cover property\n"
          "    (@(posedge clk) disable iff (rst) req |=> ack) hits++;\n"),
      f, "hits");
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->category, CoverStatementCategory::kProperty);
  EXPECT_EQ(record->scope, "t.implied");
  EXPECT_EQ(record->line, 7u);
  EXPECT_EQ(record->attempted, 9u);
  EXPECT_EQ(record->succeeded, 2u);
  EXPECT_EQ(record->vacuous, 5u);
}

TEST(CoverStatementRun, ADisabledAttemptIsCountedAndRunsNoPassStatement) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CoverSource("  always_on: cover property\n"
                  "    (@(posedge clk) disable iff (rst) 1) hits++;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 8u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->attempted, 9u);
  EXPECT_EQ(record->succeeded, 8u);
  EXPECT_EQ(record->vacuous, 0u);
}

TEST(CoverStatementRun, ABooleanCoverPropertySucceedsWhereItIsTrue) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CoverSource("  acked: cover property (@(posedge clk) ack) hits++;\n"), f,
      "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 4u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->attempted, 9u);
  EXPECT_EQ(record->succeeded, 4u);
  EXPECT_EQ(record->vacuous, 0u);
}

TEST(CoverStatementRun, ThePassStatementRunsInTheReactiveRegion) {
  SimFixture f;
  auto* reactive_hits =
      RunAndFindVar(CoverSource("  acked: cover property (@(posedge clk) ack)\n"
                                "    if (marker == $time) reactive_hits++;\n"),
                    f, "reactive_hits");
  ASSERT_NE(reactive_hits, nullptr);
  EXPECT_EQ(reactive_hits->value.ToUint64(), 4u);
}

TEST(CoverStatementRun, ACoverSequencesPassStatementRunsForEveryMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CoverSource("  matched: cover sequence\n"
                  "    (@(posedge clk) req ##[1:2] ack) hits++;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 4u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->category, CoverStatementCategory::kSequence);
  EXPECT_EQ(record->attempted, 9u);
  EXPECT_EQ(record->matched, 4u);
}

std::string NamedSequenceCoverSource(const std::string& sequence) {
  return "module t;\n"
         "  logic clk = 0; int tick = 1, hits = 0; logic c, d;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign c = tick inside {21};\n"
         "  assign d = tick inside {22, 23};\n"
         "  sequence e; @(posedge clk) " +
         sequence +
         "; endsequence\n"
         "  cover sequence (e) hits++;\n"
         "  initial #300 $finish;\n"
         "endmodule\n";
}

TEST(CoverStatementRun, ACoverOfANamedSequenceInstanceCountsEveryMatch) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(NamedSequenceCoverSource("c ##[1:2] d"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->attempted, 30u);
  EXPECT_EQ(record->matched, 2u);
}

TEST(CoverStatementRun, ANamedSequencesAttachedCallRunsAtEveryCoveredMatch) {
  SimFixture f;
  std::string out = RunCapture(
      NamedSequenceCoverSource("(c ##[1:2] d, $display(\"end %0d\", tick))"),
      f);
  EXPECT_EQ(out, "end 22\nend 23\n$finish at time 300\n");
}

TEST(CoverStatementRun, AMatchCompletingAfterTheDisableConditionIsNotCounted) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CoverSource("  matched: cover sequence\n"
                  "    (@(posedge clk) disable iff (rst) req ##[1:2] ack)\n"
                  "    hits++;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->attempted, 9u);
  EXPECT_EQ(record->matched, 3u);
}

TEST(CoverStatementRun, ACoverOfANamedPropertyInstanceReportsNoFailure) {
  SimFixture f;
  std::string out =
      RunCapture(CoverSource("  property p;\n"
                             "    @(posedge clk) req |=> ack;\n"
                             "  endproperty\n"
                             "  named: cover property (p) hits++;\n"),
                 f);
  EXPECT_EQ(out, "$finish at time 90\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
  auto* hits = f.ctx.FindVariable("hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 8u);
  const ConcurrentCoverResult* record = TheRecord(f);
  ASSERT_NE(record, nullptr);
  EXPECT_EQ(record->succeeded, 2u);
  EXPECT_EQ(record->vacuous, 6u);
}

TEST(CoverStatementRun, TheReportNamesEachStatementsCategoryAndCounts) {
  SimFixture f;
  RunAndFindVar(CoverSource("  acked: cover property (@(posedge clk) ack);\n"
                            "  matched: cover sequence\n"
                            "    (@(posedge clk) req ##[1:2] ack);\n"),
                f, "hits");
  std::ostringstream report;
  ReportConcurrentCoverResults(f.ctx.ConcurrentCovers(), report);
  EXPECT_EQ(
      report.str(),
      "cover property t.acked (line 7): attempted 9, succeeded 4, succeeded "
      "vacuously 0\n"
      "cover sequence t.matched (line 8): attempted 9, matched 4\n");
}

}  // namespace
