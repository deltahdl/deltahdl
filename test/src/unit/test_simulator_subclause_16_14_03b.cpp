#include <gtest/gtest.h>

#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

// A module around the cover statements given, as
// test/src/e2e/cover_statement.sv is: clk rises at 5, 15, ..., 85, so each
// statement attempts nine times; req is high at 15, 45 and 75, ack at 25,
// 35, 55 and 65, and rst across 65; marker is written the tick's time in
// the Active region; the run ends at 90.
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

// The one results record the run kept, or nullptr where it kept none or
// more than one.
const ConcurrentCoverResult* TheRecord(SimFixture& f) {
  const auto& results = f.ctx.ConcurrentCovers().Results();
  return results.size() == 1 ? &results[0] : nullptr;
}

// §16.14.3: the pass statement of a cover property runs once for each
// successful evaluation attempt, the attempts that succeed vacuously among
// them: req |=> ack succeeds at 25 and 55, vacuously at 5, 25, 35, 55 and
// 85, is disabled at 65 and fails at 85.
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

// §16.14.3: the results of a cover property are the attempts, the
// disabled evaluation among them, the successes, at most one per attempt,
// and the successes because of vacuity, neither counting the disabled
// evaluation.
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

// §16.14.3: a disabled evaluation is an attempt and no success, and runs no
// pass statement: a true property disabled across 65 succeeds at the eight
// other ticks.
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

// §16.14.3: a cover property in the boolean form succeeds where the
// boolean is true, never vacuously: ack is high at four ticks.
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

// §16.14.3: the pass statement runs in the Reactive region of the time
// step the attempt succeeds in, after the Active region an always
// procedure writes marker in, so it reads the tick's time there each time.
TEST(CoverStatementRun, ThePassStatementRunsInTheReactiveRegion) {
  SimFixture f;
  auto* reactive_hits =
      RunAndFindVar(CoverSource("  acked: cover property (@(posedge clk) ack)\n"
                                "    if (marker == $time) reactive_hits++;\n"),
                    f, "reactive_hits");
  ASSERT_NE(reactive_hits, nullptr);
  EXPECT_EQ(reactive_hits->value.ToUint64(), 4u);
}

// §16.14.3: the pass statement of a cover sequence runs, with multiplicity,
// once for each match of an attempt, and the results count every match:
// the attempt of 15 of req ##[1:2] ack matches at 25 and again at 35, and
// the attempt of 45 at 55 and 65.
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

// §16.14.3: a match that completes after the disable condition occurred is
// not counted: with rst high across 65, the attempt of 45 matches at 55
// alone, and the attempt of 65 is an attempt still.
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

// §16.14.3: a cover property whose spec is an instance of a named property
// monitors coverage as the boolean form does, so the attempt of 75, which
// fails at 85, is reported as no failure.
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

// §16.14.3: the tool reports the results at the end of simulation, one line
// per statement in the order they first attempted, each named by its label
// as %m in its pass statement would name it, a cover property's with its
// three counts and a cover sequence's with its two, the null pass statement
// of a cover being no bar to its results.
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
