// Tests for IEEE 1800-2023 §40.3.2.4 "$coverage_merge".
//
// $coverage_merge(coverage_type, "name") loads and merges coverage data of the
// given coverage type from a named coverage database into the simulation.
// `name` is an arbitrary, implementation-specific locator for the database. The
// integer result is one of the §40.3.1 status values:
//   `SV_COV_OK    — the data were found (for this design) and merged.
//   `SV_COV_NOCOV — the data were found but did not contain the requested type.
//   `SV_COV_ERROR — the name does not exist, the data are from a different
//                   design, or another error occurred. §40.3.2.4 requires an
//                   error when the name does not exist or is from a different
//                   design.
//
// Each test drives a real $coverage_merge system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageMerge), so the reported value is produced by the production
// evaluation path, not by invoking the model directly. The named databases a
// tool would find on disk are the one piece of state a real coverage engine
// supplies; the tests prime them the way that engine would.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_coverage_syscall.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 coverage-type constants (first argument).
constexpr int kAssertion = 20;
constexpr int kToggle = 23;

// §40.3.1 status values that $coverage_merge can report, as signed integers.
constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);

constexpr std::string_view kName = "run.cov";

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// `SV_COV_OK: a database that belongs to this design and holds the requested
// coverage type is found and merged. The merge actually happens — it is not
// merely reported — so the merge count for that database advances.
TEST(CoverageMerge, FoundForThisDesignMergesAndReportsOk) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), /*from_this_design=*/true,
                                  {kToggle, kAssertion});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 1u);
}

// `SV_COV_NOCOV: a database that is found and belongs to this design but does
// not contain the requested coverage type has nothing of that type to merge, so
// no merge is performed.
TEST(CoverageMerge, FoundButMissingTypeReportsNoCoverage) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), /*from_this_design=*/true,
                                  {kToggle});

  // The database holds toggle coverage but not assertion coverage.
  EXPECT_EQ(RunMerge(f, kAssertion, kName), kNoCov);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 0u);
}

// `SV_COV_ERROR: §40.3.2.4 requires an error when the name does not correspond
// to any saved database.
TEST(CoverageMerge, UnknownNameReportsError) {
  SimFixture f;
  EXPECT_EQ(RunMerge(f, kToggle, "nonesuch.cov"), kError);
}

// `SV_COV_ERROR: §40.3.2.4 requires an error when the database is found but
// does not correspond to the design being simulated.
TEST(CoverageMerge, DatabaseFromAnotherDesignReportsError) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName),
                                  /*from_this_design=*/false, {kToggle});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);
  EXPECT_EQ(Cov(f).MergeCount(std::string(kName)), 0u);
}

// `SV_COV_ERROR edge: a call with no arguments cannot name a coverage type and
// is a bad argument.
TEST(CoverageMerge, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_merge", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

// §40.3.2.4 "loads and merges coverage data ... into the simulator", so a merge
// that reports `SV_COV_OK leaves the simulation holding what the database held:
// the covered-item counts it was written with become part of the coverage this
// simulation reports, which is the only sense in which the data were loaded
// rather than merely located.
TEST(CoverageMerge, LoadsTheCoverageDataIntoTheSimulation) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), /*from_this_design=*/true,
                                  {kToggle});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut.u1", kToggle, 4);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  // The named instance alone holds what the database recorded against it, and
  // the hierarchy below it holds the rest.
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, /*include_below=*/false), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 10);
}

// The call names one coverage type, and that is the coverage it loads: a
// database holding data of several types leaves the types the merge did not ask
// for where they were, so a later merge of another type is what brings that one
// in.
TEST(CoverageMerge, LoadsOnlyTheCoverageTypeTheCallNames) {
  SimFixture f;
  Cov(f).RegisterCoverageDatabase(std::string(kName), /*from_this_design=*/true,
                                  {kToggle, kAssertion});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kAssertion, 3);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), 6);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kAssertion), kNoCov);

  EXPECT_EQ(RunMerge(f, kAssertion, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kAssertion), 3);
}

// A merge combines the loaded data with the coverage the simulation has already
// collected rather than replacing it: coverage data are the items covered, and
// merging two sets of them cannot lose an item either side had. So the scope
// where this simulation has covered more than the database keeps its own count,
// and the scope where the database has more takes the database's.
TEST(CoverageMerge, CombinesWithCoverageAlreadyCollected) {
  SimFixture f;
  Cov(f).SetCoveredItems("top.dut", kToggle, 9);
  Cov(f).SetCoveredItems("top.dut.u1", kToggle, 1);
  Cov(f).RegisterCoverageDatabase(std::string(kName), /*from_this_design=*/true,
                                  {kToggle});
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 4);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut.u1", kToggle, 7);

  EXPECT_EQ(RunMerge(f, kToggle, kName), kOk);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle, /*include_below=*/false), 9);
  EXPECT_EQ(Cov(f).CoverageGet("top.dut.u1", kToggle), 7);
}

// A merge that reports anything but `SV_COV_OK loaded nothing, so the coverage
// this simulation reports is untouched: the database from another design that
// §40.3.2.4 requires an error for does not get to contribute its data on the
// way to that error.
TEST(CoverageMerge, AMergeThatIsNotPerformedLoadsNothing) {
  SimFixture f;
  Cov(f).SetCoverableItems("top.dut", kToggle, 10);
  Cov(f).SetDatabaseCoveredItems(std::string(kName), "top.dut", kToggle, 6);
  Cov(f).RegisterCoverageDatabase(std::string(kName),
                                  /*from_this_design=*/false, {kToggle});

  EXPECT_EQ(RunMerge(f, kToggle, kName), kError);

  EXPECT_EQ(Cov(f).CoverageGet("top.dut", kToggle), kNoCov);
}

}  // namespace
