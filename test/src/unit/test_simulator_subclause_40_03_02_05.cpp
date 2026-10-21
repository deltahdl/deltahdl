// Tests for IEEE 1800-2023 §40.3.2.5 "$coverage_save".
//
// $coverage_save(coverage_type, "name") saves the current coverage of the given
// type to the tool's coverage database under `name`, so a later
// $coverage_merge() (§40.3.2.4) with the same name can load it. Saving does not
// affect the coverage state of this simulation. The integer result is one of
// the §40.3.1 status values:
//   `SV_COV_OK    — the coverage data were successfully saved.
//   `SV_COV_NOCOV — no such coverage is available in this design (nothing
//   saved). `SV_COV_ERROR — an error occurred during the save. §40.3.2.5 then
//   requires
//                   the tool to remove the entry for `name` so a partial write
//                   cannot corrupt the database. It is not an error to
//                   overwrite a previously existing name.
//
// Each test drives a real $coverage_save system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageSave), so the reported value is produced by the production
// evaluation path, not by invoking the model directly. Which coverage types are
// available to save, and whether the tool fails the write, are the state a real
// coverage engine supplies; the tests prime them the way that engine would.

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "helpers_coverage_syscall.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 coverage-type constants (first argument).
constexpr int kAssertion = 20;
constexpr int kToggle = 23;

// §40.3.1 status values that $coverage_save can report, as signed integers.
constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);

constexpr std::string_view kName = "run.cov";

// Evaluates $coverage_save(coverage_type, "name") through the production
// evaluator and returns the reported value as a signed integer. RunMerge
// (§40.3.2.4), used to observe the save/merge round trip, comes from the shared
// helper.
int RunSave(SimFixture& f, int coverage_type, std::string_view name) {
  return RunCoverageSysCall(f, "$coverage_save", coverage_type, name);
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// `SV_COV_OK: when coverage of the requested type is available in this design,
// a save records the data and reports success. The save actually happens — it
// is not merely reported — so the save count for that database advances.
TEST(CoverageSave, AvailableTypeIsSavedAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 1u);
}

// §40.3.2.5: data saved to the database shall be retrievable later by
// $coverage_merge() supplying the same name. What comes back is the coverage
// itself rather than a database that merely exists, so the coverage levels the
// scopes stood at go into the entry and the merge puts them back - here into a
// simulation whose own coverage has since been reset, which is what leaves the
// database as the only place the levels reported afterwards can have come from.
TEST(CoverageSave, SavedDataAreRetrievableByMergeWithTheSameName) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems("top.dut", kToggle, 6);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 4);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  Cov(f).Control(CoverageControl::kReset, kToggle, "top.dut");
  ASSERT_EQ(Cov(f).CoverageGet("top.dut", kToggle), kNoCov);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 1u);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, /*include_below=*/false), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 10);
}

// §40.3.2.5 saves coverage as it stands at the moment of the call, so the entry
// holds the levels as they stood when the save ran rather than a view that
// follows collection afterwards: what the design covers after the save is not
// in it, and a merge of that name brings back the earlier state.
TEST(CoverageSave, TheEntryHoldsTheCoverageAsItStoodAtTheSave) {
  SimFixture f;
  const std::string kScope = "top.dut";
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems(kScope, kToggle, 6);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  // Collection carries on past the save, and then the simulation's own coverage
  // is cleared, leaving only what the entry holds to come back.
  Cov(f).SetCoveredItems(kScope, kToggle, 9);
  Cov(f).Control(CoverageControl::kReset, kToggle, kScope);

  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), 6);
}

// The call names one coverage type, and that is the state it saves: what the
// design has covered of another type is no part of the entry, so a merge of the
// same name does not find that type there and brings none of it back. A reset
// clears one type, so both are reset to leave only what the merge brings.
TEST(CoverageSave, SavesOnlyTheCoverageTypeTheCallNames) {
  SimFixture f;
  const std::string kScope = "top.dut";
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetCoveredItems(kScope, kToggle, 6);
  Cov(f).SetCoveredItems(kScope, kAssertion, 3);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  Cov(f).Control(CoverageControl::kReset, kToggle, kScope);
  Cov(f).Control(CoverageControl::kReset, kAssertion, kScope);

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kNoCov);
  ASSERT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kAssertion), kNoCov);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), 6);
}

// `SV_COV_NOCOV: when no coverage of the requested type is available in this
// design there is nothing to save. No entry is written, so a later merge of
// that name finds no database at all.
TEST(CoverageSave, UnavailableTypeReportsNoCoverageAndSavesNothing) {
  SimFixture f;
  // Toggle coverage is available, but assertion coverage is not.
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunSave(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 0u);
  EXPECT_EQ(RunMerge(f, kAssertion, kName), kError);
}

// `SV_COV_ERROR: an error during the save reports the error and, per §40.3.2.5,
// the tool removes the entry for `name` to preserve database integrity — even
// an entry a previous successful save wrote under that name. The removed entry
// is then no longer retrievable by a merge.
TEST(CoverageSave, ErrorRemovesTheEntryForTheName) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
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
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(RunSave(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).SaveCount(std::string(kName)), 2u);
}

// §40.3.2.5: saving coverage shall not have any effect on the state of coverage
// in this simulation. A scope that is collecting coverage, with a current
// coverage level, is unchanged by a save: it is still collecting, its
// transition counts are unchanged, and $coverage_get reports the same level.
TEST(CoverageSave, SavingDoesNotAffectCollectionState) {
  SimFixture f;
  const std::string kScope = "top";
  Cov(f).SetAvailability(kScope, kToggle, CoverageAvailability::kFull);
  Cov(f).Control(CoverageControl::kStart, kToggle, kScope);
  Cov(f).SetCoveredItems(kScope, kToggle, 7);

  const bool kCollectingBefore = Cov(f).IsCollecting(kScope, kToggle);
  const auto kStartsBefore = Cov(f).StartCount(kScope, kToggle);
  const int kLevelBefore = Cov(f).CoverageGet(kScope, kToggle);

  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).IsCollecting(kScope, kToggle), kCollectingBefore);
  EXPECT_EQ(Cov(f).StartCount(kScope, kToggle), kStartsBefore);
  EXPECT_EQ(Cov(f).CoverageGet(kScope, kToggle), kLevelBefore);
}

// `SV_COV_ERROR edge: a call with no arguments cannot name a coverage type and
// is a bad argument.
TEST(CoverageSave, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_save", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

// A module whose FSM has reached one of its three legal states before `body`
// runs and sets r1 to r3, which are then displayed. The §40.3.1 constants are
// written as their values: `SV_COV_ASSERTION 20, `SV_COV_FSM_STATE 21.
std::string FsmSaveDesign(const std::string& body) {
  return "module top;\n"
         "  parameter [1:0] /* tool enum s_e */ P = 0, Q = 1, R = 2;\n"
         "  /* tool state_vector cur enum s_e */\n"
         "  logic [1:0] cur;\n"
         "  string db;\n"
         "  int r1, r2, r3;\n"
         "  initial begin\n"
         "    cur = Q; #1\n" +
         body +
         "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
         "  end\n"
         "endmodule\n";
}

// §40.3.2.5: a design that has collected FSM state coverage has that coverage
// to save, so the save answers `SV_COV_OK and a merge of the same name finds
// it; only a type the design holds none of - assertions here, which a check of
// that type has already found none of - answers `SV_COV_NOCOV (#7526).
TEST(CoverageSave, CoverageTheDesignCollectedIsThereToSave) {
  SimFixture f;
  const std::string kOut = RunCapture(
      FsmSaveDesign("    r1 = $coverage_save(21, \"fsm.cov\");\n"
                    "    r2 = $coverage_merge(21, \"fsm.cov\");\n"
                    "    r3 = $coverage_control(3, 20, 10, \"top\");\n"
                    "    r3 = $coverage_save(20, \"none.cov\");\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 1 0\n");
}

// §40.3.2.5: the name a save is given is a string, and a string variable gives
// the one it holds, so the database is found again by that name and the empty
// name locates none (#7524).
TEST(CoverageSave, AStringVariableNamesTheDatabase) {
  SimFixture f;
  const std::string kOut =
      RunCapture(FsmSaveDesign("    db = \"var.cov\";\n"
                               "    r1 = $coverage_save(21, db);\n"
                               "    r2 = $coverage_merge(21, \"var.cov\");\n"
                               "    r3 = $coverage_merge(21, \"\");\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 1 -1\n");
}

// A run that keeps its coverage databases as files in `scratch`, its design
// one instance, `top`, of the module `top`, offering toggle coverage.
void KeepDatabasesIn(SimFixture& f, const ScratchDir& scratch) {
  Cov(f).SetDatabaseDirectory(scratch.dir.string());
  Cov(f).SetModuleDefinition("top", "top");
  Cov(f).SetAvailability("top", kToggle, CoverageAvailability::kFull);
}

// §40.3.2.5 with §40.3.2.4: a saved database is a file the name maps to, so a
// later run - a second simulation with nothing in common with the first but
// the directory and the design - merges it, and the counts it saved come back,
// the one of a scope below `top` as well as `top`'s own (#7527).
TEST(CoverageSave, ASavedDatabaseOutlivesTheRunThatSavedIt) {
  ScratchDir scratch;
  {
    SimFixture first;
    KeepDatabasesIn(first, scratch);
    Cov(first).SetCoveredItems("top", kToggle, 6);
    Cov(first).SetCoveredItems("top.inner", kToggle, 1);
    ASSERT_EQ(RunSave(first, kToggle, kName), kOk);
  }
  SimFixture later;
  KeepDatabasesIn(later, scratch);

  EXPECT_EQ(RunMerge(later, kToggle, kName), kOk);
  EXPECT_EQ(Cov(later).CoverageGet("top", kToggle, /*include_below=*/false), 6);
  EXPECT_EQ(Cov(later).CoverageGet("top", kToggle), 7);
}

// §40.3.2.5: a database file that cannot be written is an error during the
// save, and the entry goes with it, so the name merges nothing (#7527).
TEST(CoverageSave, ADatabaseThatCannotBeWrittenIsAnError) {
  ScratchDir scratch;
  SimFixture f;
  KeepDatabasesIn(f, scratch);
  Cov(f).SetDatabaseDirectory((scratch.dir / "absent").string());

  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
}

// §40.3.2.5: an error during a save removes the database entry for the name,
// and the entry is a file, so the file an earlier save wrote is gone (#7527).
TEST(CoverageSave, AFailedSaveRemovesTheDatabaseFile) {
  ScratchDir scratch;
  SimFixture f;
  KeepDatabasesIn(f, scratch);
  ASSERT_EQ(RunSave(f, kToggle, kName), kOk);
  ASSERT_TRUE(std::filesystem::exists(scratch.dir / std::string(kName)));

  Cov(f).SetCoverageSaveShouldFail(true);
  EXPECT_EQ(RunSave(f, kToggle, kName), kError);
  EXPECT_FALSE(std::filesystem::exists(scratch.dir / std::string(kName)));
}

}  // namespace
