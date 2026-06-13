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
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 coverage-type constants (first argument).
constexpr int kAssertion = 20;
constexpr int kToggle = 23;

// §40.3.1 status values that $coverage_merge can report, as signed integers.
constexpr int kOk = static_cast<int>(CoverageStatus::Ok);
constexpr int kError = static_cast<int>(CoverageStatus::Error);
constexpr int kNoCov = static_cast<int>(CoverageStatus::NoCoverage);

constexpr std::string_view kName = "run.cov";

// Evaluates $coverage_merge(coverage_type, "name") through the production
// evaluator and returns the reported value as a signed integer.
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

// `SV_COV_ERROR: §40.3.2.4 requires an error when the database is found but does
// not correspond to the design being simulated.
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

}  // namespace
