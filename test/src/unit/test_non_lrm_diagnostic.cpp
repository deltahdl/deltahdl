#include <gtest/gtest.h>

#include <cstdint>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"

using namespace delta;

namespace {

// No clause of IEEE 1800-2023 says what a tool keeps about the diagnostics it
// has reported, so these cases cover DiagEngine on its own terms. What they
// establish is that a caller can tell one reported failure from another: the
// counts beside the records say how many errors there were and never which
// error, so an assertion that a run failed for the reason under test has to
// read the record itself.

// One real file for the diagnostics to be reported against, so a record
// carries a location it could have got wrong. Every case reports at a line and
// a column that differ from each other and from zero, so a record that dropped
// either of the two, or that kept the location a default-constructed record
// carries, reads differently from one that kept what it was given.
struct EngineFixture {
  SourceManager mgr;
  uint32_t file_id = mgr.AddFile("cell.sv",
                                 "module one_cell;\n"
                                 "endmodule\n");
  DiagEngine diag{mgr};

  SourceLoc Loc(uint32_t line, uint32_t column) const {
    return SourceLoc{file_id, line, column};
  }
};

TEST(Diagnostics, ErrorIsRecordedWithItsMessage) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "two libraries claim this description");
  EXPECT_EQ(f.diag.Diagnostics().front().loc.line, 2u);
  EXPECT_EQ(f.diag.Diagnostics().front().loc.column, 4u);
}

TEST(Diagnostics, ErrorIsRecordedWithItsSeverity) {
  // A Diagnostic carries kError as its default severity, so a record that was
  // never given a severity at all still reads as an error. The warning
  // reported first is what makes the claim able to fail: code that stamped one
  // severity on every record it kept would have to stamp it on that one too.
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Clause::None());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().severity, DiagSeverity::kError);
  EXPECT_NE(f.diag.Diagnostics().front().severity,
            f.diag.Diagnostics().back().severity);
}

TEST(Diagnostics, WarningIsRecordedWithItsSeverity) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kWarning);
}

TEST(Diagnostics, RecordsAreReturnedInTheOrderTheyWereReported) {
  // Two descriptions of one run fail for different reasons. A caller reading
  // the records back attributes each reason to the step that reported it, so
  // the order the records come in is the order they were reported in.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Clause::None());
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body", Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "cannot read source description: absent.v");
  EXPECT_EQ(f.diag.Diagnostics().back().message,
            "unexpected token in module body");
}

TEST(Diagnostics, SuppressedDiagnosticIsNotRecorded) {
  // A speculative parse whose result is discarded reports errors that never
  // happened, and the engine suppresses them. The record it keeps has to
  // respect the suppression the counts already respect, or a caller reading
  // the records back learns of a failure the run did not have. The error
  // reported before the suppression is what shows the records were being kept
  // at all.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Clause::None());
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body", Clause::None());
  f.diag.PopSuppress();

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "cannot read source description: absent.v");
}

// A clause of IEEE 1800-2023 is what the engine reports a rule from, and the
// cases below cover the record keeping it. The clause a report names is
// separate from the sentence it reads out, so a caller can ask which rule was
// enforced without matching the wording of the sentence, and a reworded
// message leaves the answer alone. Every case names a clause of three
// components, since clause numbering is not arithmetic and code that stored it
// as a number would lose the third.

TEST(Diagnostics, ClauseNamedInTheReportIsRecorded) {
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause("11.4.14"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().clause, "11.4.14");
}

TEST(Diagnostics, ClauseReportedWithAWarningIsRecorded) {
  // A warning enforces a rule as much as an error does, so the clause survives
  // the path through the engine that an error does not take.
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Clause("16.12.17"));

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().clause, "16.12.17");
}

TEST(Diagnostics, ReportStatingNoRuleOfTheStandardCarriesAnEmptyClause) {
  // A report that enforces no rule of the standard says so with
  // Clause::None(), and it has to read back as naming none rather than as
  // naming whatever the last report named. The clause-bearing error reported
  // first is what makes that able to fail: an engine holding the clause across
  // reports would hand it to the second one. Clause::Unread() is covered by
  // the same case, since the two are one value at run time and differ only in
  // the word the source uses.
  EngineFixture f;
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause("11.4.14"));
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v",
               Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().clause, "");
}

TEST(Diagnostics, ClauseIsPrintedWithTheMessage) {
  // A field nothing prints helps a test and no user, so the clause reaches the
  // reader of the diagnostic as well as the reader of the record. Diagnostics
  // are written to standard error, which the case redirects for the one report
  // it makes.
  EngineFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause("11.4.14"));
  std::cerr.rdbuf(old_buf);

  EXPECT_NE(captured.str().find("two libraries claim this description"),
            std::string::npos);
  EXPECT_NE(captured.str().find("(§11.4.14)"), std::string::npos);
}

TEST(Diagnostics, SuppressedDiagnosticWithAClauseIsNotRecorded) {
  // A speculative parse reports rules broken by source the run goes on to
  // discard, and naming the clause does not make one of those reports real.
  // The engine returns before it appends, so this holds today; the case is
  // what keeps a later edit from treating a clause-bearing diagnostic as a
  // case worth recording through the suppression.
  EngineFixture f;
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description",
               Clause("11.4.14"));
  f.diag.PopSuppress();

  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(Diagnostics, WarningPromotedToAnErrorIsRecordedAsAnError) {
  // An invocation that asked for warnings to be errors gets a record saying
  // error, matching the count the same warning is added to. Without the
  // promotion this warning is recorded as a warning, which is what the case
  // above establishes.
  EngineFixture f;
  f.diag.SetWarningsAsErrors(true);
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written",
                 Clause::None());

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kError);
}

}  // namespace
