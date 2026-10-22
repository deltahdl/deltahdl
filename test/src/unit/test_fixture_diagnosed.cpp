// Tests over lib/cpp/test_fixtures/fixture_diagnosed.h itself.
//
// Diagnosed is what fails a case that handed a fixture a source deltahdl
// rejected and never read the diagnostics, so a defect in it either lets such
// a case go on passing or fails cases that did read them. The cases below
// drive it over a bare DiagEngine, standing in for the fixture that would own
// both.
//
// A case below that asserts Diagnosed stayed quiet needs no macro saying so.
// It reports through ADD_FAILURE as it is destroyed, which fails whichever case
// is running, so a report raised when none was owed fails the case that built
// it. A case asserting that it did report builds it inside a function of its
// own and hands the call to EXPECT_NONFATAL_FAILURE, from gtest/gtest-spi.h,
// so the destruction falls inside the statement the macro watches and exactly
// one report is expected of it.

#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"

using namespace delta;

namespace {

constexpr const char* kSource =
    "module m;\n"
    "  logic x\n"
    "endmodule\n";

// The engine a fixture would own, with the source above to report against.
struct Engine {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("<test>", kSource);
  DiagEngine diag{mgr};

  void ReportError() {
    diag.Error(SourceLoc{file_id, 3, 1}, "expected ';'", Subclause::None());
  }
};

constexpr const char* kUnreadReport =
    "the source drew an error the case never read";

void HandOverAnErrorNobodyReads() {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);
}

TEST(Diagnosed, AnErrorHandedOverAndNeverReadFailsTheCase) {
  EXPECT_NONFATAL_FAILURE(HandOverAnErrorNobodyReads(), kUnreadReport);
}

// The report has to say which input to look at and what was wrong with it, or
// whoever reads the failure is sent to the harness instead of to the case.
TEST(Diagnosed, TheReportNamesTheSourceAndTheErrorItDrew) {
  EXPECT_NONFATAL_FAILURE(HandOverAnErrorNobodyReads(), "  logic x\n");
  EXPECT_NONFATAL_FAILURE(HandOverAnErrorNobodyReads(), "line 3: expected ';'");
}

TEST(Diagnosed, ReadingTheAnswerAfterTheHandoverDischargesIt) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);

  EXPECT_TRUE(outcome);
}

// Hands over a rejected source and then queries the engine with `read`, as a
// case does that reads f.diag rather than has_errors.
void HandOverThenQuery(void (*read)(const DiagEngine&)) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);
  read(e.diag);
}

// Each query of the engine discharges the obligation, as reading has_errors
// does: counting only some of them is what failed every case that read the
// rejection through f.diag.HasErrors() in the first attempt at this check.
TEST(Diagnosed, AnyQueryOfTheEngineAfterTheHandoverDischargesIt) {
  HandOverThenQuery(
      [](const DiagEngine& d) { static_cast<void>(d.HasErrors()); });
  HandOverThenQuery(
      [](const DiagEngine& d) { static_cast<void>(d.ErrorCount()); });
  HandOverThenQuery(
      [](const DiagEngine& d) { static_cast<void>(d.WarningCount()); });
  HandOverThenQuery(
      [](const DiagEngine& d) { static_cast<void>(d.Diagnostics()); });
  HandOverThenQuery(
      [](const DiagEngine& d) { static_cast<void>(d.SuppressedErrorCount()); });
}

// A fixture reads the engine while it compiles, before it hands the source
// over, and those reads are its own. Counting them would discharge the
// obligation of every case before the case had run a line.
void QueryThenHandOver() {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  static_cast<void>(e.diag.Diagnostics());
  outcome.Record(kSource);
}

TEST(Diagnosed, AQueryBeforeTheHandoverDoesNotDischargeIt) {
  EXPECT_NONFATAL_FAILURE(QueryThenHandOver(), kUnreadReport);
}

// A case that compiles on the fixture's engine itself hands nothing over, and
// an error it never queries is unread all the same.
void ReportAnErrorNobodyQueries() {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
}

TEST(Diagnosed, AnErrorNoQueryFollowsFailsTheCaseWithoutAHandover) {
  EXPECT_NONFATAL_FAILURE(ReportAnErrorNobodyQueries(), kUnreadReport);
}

TEST(Diagnosed, AnErrorAQueryFollowsDischargesItWithoutAHandover) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();

  static_cast<void>(e.diag.ErrorCount());
}

// The source was accepted and the case read that it was, and then running it
// reported an error the case never looked at.
void ReportAnErrorAfterAReadHandover() {
  Engine e;
  Diagnosed outcome{e.diag};
  outcome.Record(kSource);
  EXPECT_FALSE(outcome);
  e.ReportError();
}

TEST(Diagnosed, AnErrorReportedAfterTheHandoverAndNeverReadFailsTheCase) {
  EXPECT_NONFATAL_FAILURE(ReportAnErrorAfterAReadHandover(), kUnreadReport);
}

TEST(Diagnosed, AnAcceptedSourceNeverReadRaisesNothing) {
  Engine e;
  Diagnosed outcome{e.diag};
  outcome.Record(kSource);
}

TEST(Diagnosed, AWarningNeverReadRaisesNothing) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.diag.Warning(SourceLoc{e.file_id, 1, 1}, "module has no ports",
                 Subclause::None());
  outcome.Record(kSource);
}

// A fixture that has already failed the case over its source, as ElaborateSrc
// does when the source did not parse, excuses the second report.
TEST(Diagnosed, AnExcusedHandoverRaisesNothing) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);

  outcome.Excuse();
}

// EXPECT_NONFATAL_FAILURE expects exactly one report, so a move that left the
// obligation on both objects fails here as much as one that dropped it.
void MoveAnUnreadHandover() {
  Engine e;
  Diagnosed first{e.diag};
  e.ReportError();
  first.Record(kSource);
  Diagnosed second(std::move(first));
}

TEST(Diagnosed, AMoveCarriesTheObligationAndRaisesItOnce) {
  EXPECT_NONFATAL_FAILURE(MoveAnUnreadHandover(), kUnreadReport);
}

// A case that compiled the source itself records the answer by assigning it,
// and the read that produced the answer is part of that handover.
void AssignAnAnswerNobodyReads() {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome = e.diag.HasErrors();
}

TEST(Diagnosed, AnAssignedAnswerIsAHandoverOfItsOwn) {
  EXPECT_NONFATAL_FAILURE(AssignAnAnswerNobodyReads(), kUnreadReport);
}

}  // namespace
