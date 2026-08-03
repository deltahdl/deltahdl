#include <gtest/gtest.h>

#include <cstdint>

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
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description");

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
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written");
  f.diag.Error(f.Loc(2, 4), "two libraries claim this description");

  ASSERT_EQ(f.diag.Diagnostics().size(), 2u);
  EXPECT_EQ(f.diag.Diagnostics().back().severity, DiagSeverity::kError);
  EXPECT_NE(f.diag.Diagnostics().front().severity,
            f.diag.Diagnostics().back().severity);
}

TEST(Diagnostics, WarningIsRecordedWithItsSeverity) {
  EngineFixture f;
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written");

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kWarning);
}

TEST(Diagnostics, RecordsAreReturnedInTheOrderTheyWereReported) {
  // Two descriptions of one run fail for different reasons. A caller reading
  // the records back attributes each reason to the step that reported it, so
  // the order the records come in is the order they were reported in.
  EngineFixture f;
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v");
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body");

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
  f.diag.Error(f.Loc(1, 8), "cannot read source description: absent.v");
  f.diag.PushSuppress();
  f.diag.Error(f.Loc(2, 4), "unexpected token in module body");
  f.diag.PopSuppress();

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().message,
            "cannot read source description: absent.v");
}

TEST(Diagnostics, WarningPromotedToAnErrorIsRecordedAsAnError) {
  // An invocation that asked for warnings to be errors gets a record saying
  // error, matching the count the same warning is added to. Without the
  // promotion this warning is recorded as a warning, which is what the case
  // above establishes.
  EngineFixture f;
  f.diag.SetWarningsAsErrors(true);
  f.diag.Warning(f.Loc(1, 8), "cell name collides with one already written");

  ASSERT_EQ(f.diag.Diagnostics().size(), 1u);
  EXPECT_EQ(f.diag.Diagnostics().front().severity, DiagSeverity::kError);
}

}  // namespace
