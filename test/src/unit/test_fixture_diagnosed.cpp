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

void HandOverThenQuery(void (*read)(const DiagEngine&)) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);
  read(e.diag);
}

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

TEST(Diagnosed, AnExcusedHandoverRaisesNothing) {
  Engine e;
  Diagnosed outcome{e.diag};
  e.ReportError();
  outcome.Record(kSource);

  outcome.Excuse();
}

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
