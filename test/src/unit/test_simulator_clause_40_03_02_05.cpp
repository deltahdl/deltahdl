// Tests for IEEE 1800-2023 §40.3.2.5 "$coverage_save".
//
// $coverage_save(coverage_type, "name") saves the current coverage of the given
// type to the tool's coverage database under `name`, so a later
// $coverage_merge() (§40.3.2.4) with the same name can load it. Saving does not
// affect the coverage state of this simulation. The integer result is one of the
// §40.3.1 status values:
//   `SV_COV_OK    — the coverage data were successfully saved.
//   `SV_COV_NOCOV — no such coverage is available in this design (nothing saved).
//   `SV_COV_ERROR — an error occurred during the save. §40.3.2.5 then requires
//                   the tool to remove the entry for `name` so a partial write
//                   cannot corrupt the database. It is not an error to overwrite
//                   a previously existing name.
//
// Each test drives a real $coverage_save system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageSave), so the reported value is produced by the production
// evaluation path, not by invoking the model directly. Which coverage types are
// available to save, and whether the tool fails the write, are the state a real
// coverage engine supplies; the tests prime them the way that engine would.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 coverage-type constants (first argument).
constexpr int kAssertion = 20;
constexpr int kToggle = 23;

// §40.3.1 status values that $coverage_save can report, as signed integers.
constexpr int kOk = static_cast<int>(CoverageStatus::Ok);
constexpr int kError = static_cast<int>(CoverageStatus::Error);
constexpr int kNoCov = static_cast<int>(CoverageStatus::NoCoverage);

constexpr std::string_view kName = "run.cov";

// Evaluates $coverage_save(coverage_type, "name") through the production
// evaluator and returns the reported value as a signed integer.
int RunSave(SimFixture& f, int coverage_type, std::string_view name) {
  auto* call = MkSysCall(
      f.arena, "$coverage_save",
      {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkStr(f.arena, name)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

// Evaluates $coverage_merge(coverage_type, "name") through the production
// evaluator (§40.3.2.4), used to observe the save/merge round trip.
int RunMerge(SimFixture& f, int coverage_type, std::string_view name) {
  auto* call = MkSysCall(
      f.arena, "$coverage_merge",
      {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkStr(f.arena, name)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// `SV_COV_OK: when coverage of the requested type is available in this design, a
// save records the data and reports success. The save actually happens — it is
// not merely reported — so the save count for that database advances.
TEST(CoverageSave, AvailableTypeIsSavedAndReportsOk) {
  SimFixture f;
  Cov(f).SetCoverageAvailableForSave(kToggle, true);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 1u);
}

// §40.3.2.5: data saved to the database shall be retrievable later by
// $coverage_merge() supplying the same name. After a successful save, a merge of
// the same type and name finds the data (for this design) and merges it.
TEST(CoverageSave, SavedDataAreRetrievableByMergeWithTheSameName) {
  SimFixture f;
  Cov(f).SetCoverageAvailableForSave(kToggle, true);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 1u);
}

// `SV_COV_NOCOV: when no coverage of the requested type is available in this
// design there is nothing to save. No entry is written, so a later merge of that
// name finds no database at all.
TEST(CoverageSave, UnavailableTypeReportsNoCoverageAndSavesNothing) {
  SimFixture f;
  // Toggle coverage is available, but assertion coverage is not.
  Cov(f).SetCoverageAvailableForSave(kToggle, true);

  EXPECT_EQ(RunSave(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 0u);
  EXPECT_EQ(RunMerge(f, kAssertion, kName), kError);
}

// `SV_COV_ERROR: an error during the save reports the error and, per §40.3.2.5,
// the tool removes the entry for `name` to preserve database integrity — even an
// entry a previous successful save wrote under that name. The removed entry is
// then no longer retrievable by a merge.
TEST(CoverageSave, ErrorRemovesTheEntryForTheName) {
  SimFixture f;
  Cov(f).SetCoverageAvailableForSave(kToggle, true);
  // A prior successful save leaves an entry under the name.
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);

  // The next save fails; the entry being written for the name is removed.
  Cov(f).SetCoverageSaveShouldFail(true);
  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 0u);
  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
}

// §40.3.2.5: it is not an error to overwrite a previously existing name. Saving
// again to a name that already holds saved data reports success and records the
// rewrite.
TEST(CoverageSave, OverwritingAnExistingNameIsNotAnError) {
  SimFixture f;
  Cov(f).SetCoverageAvailableForSave(kToggle, true);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 2u);
}

// §40.3.2.5: saving coverage shall not have any effect on the state of coverage
// in this simulation. A scope that is collecting coverage, with a current
// coverage level, is unchanged by a save: it is still collecting, its transition
// counts are unchanged, and $coverage_get reports the same level.
TEST(CoverageSave, SavingDoesNotAffectCollectionState) {
  SimFixture f;
  const std::string scope = "top";
  Cov(f).SetAvailability(scope, CoverageAvailability::Full);
  Cov(f).Control(CoverageControl::Start, scope);
  Cov(f).SetCoveredItems(scope, kToggle, 7);
  Cov(f).SetCoverageAvailableForSave(kToggle, true);

  const bool collecting_before = Cov(f).IsCollecting(scope);
  const auto starts_before = Cov(f).StartCount(scope);
  const int level_before = Cov(f).CoverageGet(scope, kToggle);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).IsCollecting(scope), collecting_before);
  EXPECT_EQ(Cov(f).StartCount(scope), starts_before);
  EXPECT_EQ(Cov(f).CoverageGet(scope, kToggle), level_before);
}

// `SV_COV_ERROR edge: a call with no arguments cannot name a coverage type and is
// a bad argument.
TEST(CoverageSave, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_save", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

}  // namespace
