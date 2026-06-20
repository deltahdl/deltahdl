// Tests for IEEE 1800-2023 §40.3.2.1 "$coverage_control".
//
// $coverage_control(control_constant, coverage_type, scope_def,
// modules_or_instance) starts, stops, resets, or queries coverage collection
// over a portion of the hierarchy and returns one of the §40.3.1 status values.
//
// Each test drives a real $coverage_control system-function call through the
// simulator's expression evaluator (EvalExpr -> EvalVerifSysCall ->
// EvalCoverageControl), so the reported status and any state change are
// produced by the production evaluation path, not by invoking the model
// directly. The coverage available in a scope is the one piece of state a real
// coverage engine would supply; the tests prime it the way that engine would.

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 control constants (first argument).
constexpr int kStart = 0;
constexpr int kStop = 1;
constexpr int kReset = 2;
constexpr int kCheck = 3;

// §40.3.1 status values, as signed integers.
constexpr int kOk = static_cast<int>(CoverageStatus::Ok);
constexpr int kError = static_cast<int>(CoverageStatus::Error);
constexpr int kNoCov = static_cast<int>(CoverageStatus::NoCoverage);
constexpr int kPartial = static_cast<int>(CoverageStatus::Partial);

constexpr std::string_view kScope = "$root.tb.unit1";

// Evaluates $coverage_control(control, `SV_COV_TOGGLE, `SV_COV_HIER, scope)
// through the production evaluator and returns the reported status as a signed
// integer. The coverage_type and scope_def arguments are passed as the §40.3.1
// constants a real caller would use.
int RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call =
      MkSysCall(f.arena, "$coverage_control",
                {MkInt(f.arena, static_cast<uint64_t>(control)),
                 MkInt(f.arena, 23 /* `SV_COV_TOGGLE */),
                 MkInt(f.arena, 11 /* `SV_COV_HIER */), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

// C1/C2/C4: `SV_COV_START on a fully coverable scope reports `SV_COV_OK
// (Table 40-1, START/OK column) and begins collecting.
TEST(CoverageControl, StartOnFullScopeCollectsAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
}

// C4: `SV_COV_START on a partially coverable scope reports `SV_COV_PARTIAL
// (Table 40-1, START/PARTIAL column) and still starts what it can.
TEST(CoverageControl, StartOnPartialScopeReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Partial);

  EXPECT_EQ(RunControl(f, kStart, kScope), kPartial);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
}

// C4: `SV_COV_START on a scope with no coverage of the requested type reports
// `SV_COV_NOCOV (Table 40-1, START/NOCOV column) and starts nothing.
TEST(CoverageControl, StartOnUncoverableScopeReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::None);

  EXPECT_EQ(RunControl(f, kStart, kScope), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope)));
}

// C2/C4: `SV_COV_CHECK reports whether coverage can be obtained for each
// availability (Table 40-1, CHECK row: full -> OK, partial -> PARTIAL, none ->
// NOCOV) and never begins collecting.
TEST(CoverageControl, CheckReportsAvailabilityWithoutCollecting) {
  SimFixture f;
  Cov(f).SetAvailability("full", CoverageAvailability::Full);
  Cov(f).SetAvailability("part", CoverageAvailability::Partial);
  Cov(f).SetAvailability("none", CoverageAvailability::None);

  EXPECT_EQ(RunControl(f, kCheck, "full"), kOk);
  EXPECT_EQ(RunControl(f, kCheck, "part"), kPartial);
  EXPECT_EQ(RunControl(f, kCheck, "none"), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting("full"));
}

// C2/C4: `SV_COV_STOP halts an active collection and reports success.
TEST(CoverageControl, StopHaltsCollectionAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope)));
}

// C2/C4: `SV_COV_RESET clears collected coverage and reports success.
TEST(CoverageControl, ResetClearsCoverageAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 1U);
}

// C5 (shall): starting a scope whose coverage is already started has no effect.
// The redundant start does not advance the start transition count and still
// reports success.
TEST(CoverageControl, RepeatedStartHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
  EXPECT_EQ(Cov(f).StartCount(std::string(kScope)), 1U);
}

// C6 (shall): repeated stops have no effect.
TEST(CoverageControl, RepeatedStopHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(Cov(f).StopCount(std::string(kScope)), 1U);
}

// C6 (shall): repeated resets have no effect; once coverage is cleared the
// second reset finds nothing to clear.
TEST(CoverageControl, RepeatedResetHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 1U);
}

// C2: a reset has no effect when no coverage is available, but still succeeds.
TEST(CoverageControl, ResetWithoutCoverageHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::None);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 0U);
}

// C7: a scope the design does not contain is a bad argument; every control
// action over an unregistered scope reports `SV_COV_ERROR (Table 40-1, ERROR
// column) and fails without any effect.
TEST(CoverageControl, UnknownScopeIsBadArgument) {
  SimFixture f;
  const std::string missing = "$root.tb.nonesuch";

  EXPECT_EQ(RunControl(f, kStart, missing), kError);
  EXPECT_EQ(RunControl(f, kStop, missing), kError);
  EXPECT_EQ(RunControl(f, kReset, missing), kError);
  EXPECT_EQ(RunControl(f, kCheck, missing), kError);

  EXPECT_FALSE(Cov(f).IsRegistered(missing));
  EXPECT_FALSE(Cov(f).IsCollecting(missing));
}

// C7 (edge): a first argument outside the four §40.3.1 control constants is a
// bad argument, reported as `SV_COV_ERROR even on a fully coverable scope.
TEST(CoverageControl, InvalidControlConstantIsBadArgument) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::Full);

  EXPECT_EQ(RunControl(f, 99, kScope), kError);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope)));
}

// C7 (edge): a call with no arguments cannot name a control action and is a bad
// argument, reported as `SV_COV_ERROR.
TEST(CoverageControl, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_control", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

}  // namespace
