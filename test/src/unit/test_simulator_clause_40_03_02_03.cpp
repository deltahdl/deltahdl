// Tests for IEEE 1800-2023 §40.3.2.3 "$coverage_get".
//
// $coverage_get(coverage_type, scope_def, modules_or_instance) obtains the
// current coverage value for the given coverage type over the named portion of
// the hierarchy — the number of coverable items of that type that have been
// covered so far. The return follows the same pattern as $coverage_get_max()
// (§40.3.2.2), so coverage% is coverage_get()/coverage_get_max() * 100, but the
// positive value is the current coverage level rather than the maximum. The
// integer result is one of the §40.3.1 status values (`SV_COV_ERROR for bad
// arguments, `SV_COV_NOCOV when no coverage is available for the type,
// `SV_COV_OVERFLOW when the count cannot be represented) or a positive current
// coverage number.
//
// Each test drives a real $coverage_get system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageGet), so the reported value is produced by the production
// evaluation path, not by invoking the model directly. The covered-item count a
// scope holds is the one piece of state a real coverage engine would accumulate
// as collection proceeds; the tests prime it the way that engine would. The
// scope is specified per $coverage_control() (§40.3.2.1).

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
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

// §40.3.1 status values that $coverage_get can report, as signed integers.
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);
constexpr int kOverflow = static_cast<int>(CoverageStatus::kOverflow);

constexpr std::string_view kScope = "$root.tb.unit1";

// Evaluates $coverage_get(coverage_type, `SV_COV_HIER, scope) through the
// production evaluator and returns the reported value as a signed integer.
int RunGet(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call =
      MkSysCall(f.arena, "$coverage_get",
                {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                 MkInt(f.arena, 11 /* `SV_COV_HIER */), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// +pos_num: with covered items of the requested type, get returns the current
// count covered, and the coverage_type argument selects which count is
// reported.
TEST(CoverageGet, ReportsCurrentCoveredCountPerType) {
  SimFixture f;
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 12);
  Cov(f).SetCoveredItems(std::string(kScope), kAssertion, 3);

  EXPECT_EQ(RunGet(f, kToggle, kScope), 12);
  EXPECT_EQ(RunGet(f, kAssertion, kScope), 3);
}

// The current coverage value is the number covered, not the maximum: with more
// items coverable than covered, get reports the covered count while get_max
// would report the larger coverable total. This is the distinction that makes
// coverage% = coverage_get()/coverage_get_max() * 100 meaningful.
TEST(CoverageGet, ReportsCoveredCountDistinctFromMaximum) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 30);

  EXPECT_EQ(RunGet(f, kToggle, kScope), 30);
}

// 0 (`SV_COV_NOCOV): a scope that exists but has covered no items of the
// requested type reports that no coverage is available, since a positive
// current coverage value is strictly greater than zero.
TEST(CoverageGet, NoCoveredItemsReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetCoveredItems(std::string(kScope), kToggle, 12);

  // No assertion items have been covered in this scope.
  EXPECT_EQ(RunGet(f, kAssertion, kScope), kNoCov);
}

// -1 (`SV_COV_ERROR): a scope the design does not contain is a bad argument and
// reports an error.
TEST(CoverageGet, UnknownScopeIsBadArgument) {
  SimFixture f;
  EXPECT_EQ(RunGet(f, kToggle, "$root.tb.nonesuch"), kError);
}

// -2 (`SV_COV_OVERFLOW): a current coverage count too large to represent as an
// integer overflows.
TEST(CoverageGet, CountExceedingIntegerRangeOverflows) {
  SimFixture f;
  Cov(f).SetCoveredItems(
      std::string(kScope), kToggle,
      static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max()) + 1);

  EXPECT_EQ(RunGet(f, kToggle, kScope), kOverflow);
}

// -1 (`SV_COV_ERROR) edge: a call with no arguments cannot name a coverage type
// and is a bad argument.
TEST(CoverageGet, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_get", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

}  // namespace
