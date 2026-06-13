// Tests for IEEE 1800-2023 §40.3.2.2 "$coverage_get_max".
//
// $coverage_get_max(coverage_type, scope_def, modules_or_instance) obtains the
// value representing 100% coverage for the given coverage type over the named
// portion of the hierarchy. That value is the sum of all coverable items of the
// type; it shall remain constant across the duration of the simulation. The
// integer result is one of the §40.3.1 status values (`SV_COV_ERROR for bad
// arguments, `SV_COV_NOCOV when no coverage is available for the type,
// `SV_COV_OVERFLOW when the count cannot be represented) or a positive maximum
// coverage number.
//
// Each test drives a real $coverage_get_max system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageGetMax), so the reported value is produced by the production
// evaluation path, not by invoking the model directly. The coverable-item count
// a scope holds is the one piece of state a real coverage engine would supply;
// the tests prime it the way that engine would. The scope is specified per
// $coverage_control() (§40.3.2.1).

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
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

// §40.3.1 control constants used to change the collection state.
constexpr int kStart = 0;
constexpr int kReset = 2;

// §40.3.1 status values that $coverage_get_max can report, as signed integers.
constexpr int kError = static_cast<int>(CoverageStatus::Error);
constexpr int kNoCov = static_cast<int>(CoverageStatus::NoCoverage);
constexpr int kOverflow = static_cast<int>(CoverageStatus::Overflow);

constexpr std::string_view kScope = "$root.tb.unit1";

// Evaluates $coverage_get_max(coverage_type, `SV_COV_HIER, scope) through the
// production evaluator and returns the reported value as a signed integer.
int RunGetMax(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_get_max",
      {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
       MkInt(f.arena, 11 /* `SV_COV_HIER */), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

// Drives a $coverage_control action over a scope through the production
// evaluator so the collection state can be changed between get_max calls.
void RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)),
       MkInt(f.arena, kToggle), MkInt(f.arena, 11 /* `SV_COV_HIER */),
       MkStr(f.arena, scope)});
  EvalExpr(call, f.ctx, f.arena);
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// +pos_num: with coverable items of the requested type, get_max returns their
// sum, and the coverage_type argument selects which count is reported.
TEST(CoverageGetMax, ReportsSumOfCoverableItemsPerType) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetCoverableItems(std::string(kScope), kAssertion, 5);

  EXPECT_EQ(RunGetMax(f, kToggle, kScope), 48);
  EXPECT_EQ(RunGetMax(f, kAssertion, kScope), 5);
}

// 0 (`SV_COV_NOCOV): a scope that exists but holds no coverable items of the
// requested type reports that no coverage is available for that type.
TEST(CoverageGetMax, NoCoverableItemsReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);

  // The toggle items do not make assertion coverage available.
  EXPECT_EQ(RunGetMax(f, kAssertion, kScope), kNoCov);
}

// -1 (`SV_COV_ERROR): a scope the design does not contain is a bad argument and
// reports an error.
TEST(CoverageGetMax, UnknownScopeIsBadArgument) {
  SimFixture f;
  EXPECT_EQ(RunGetMax(f, kToggle, "$root.tb.nonesuch"), kError);
}

// -2 (`SV_COV_OVERFLOW): a maximum coverage count too large to represent as an
// integer overflows.
TEST(CoverageGetMax, CountExceedingIntegerRangeOverflows) {
  SimFixture f;
  Cov(f).SetCoverableItems(
      std::string(kScope), kToggle,
      static_cast<std::int64_t>(std::numeric_limits<std::int32_t>::max()) + 1);

  EXPECT_EQ(RunGetMax(f, kToggle, kScope), kOverflow);
}

// shall: the value representing 100% coverage remains constant across the
// simulation. Starting and then resetting collection changes the collection
// state but not the maximum coverage number.
TEST(CoverageGetMax, MaximumStaysConstantAcrossCollectionChanges) {
  SimFixture f;
  Cov(f).SetCoverableItems(std::string(kScope), kToggle, 48);
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);

  const int before = RunGetMax(f, kToggle, kScope);
  RunControl(f, kStart, kScope);
  RunControl(f, kReset, kScope);
  const int after = RunGetMax(f, kToggle, kScope);

  EXPECT_EQ(before, 48);
  EXPECT_EQ(after, before);
}

// -1 (`SV_COV_ERROR) edge: a call with no arguments cannot name a coverage type
// and is a bad argument.
TEST(CoverageGetMax, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_get_max", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

}  // namespace
