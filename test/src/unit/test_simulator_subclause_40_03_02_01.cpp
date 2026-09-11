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
constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);
constexpr int kPartial = static_cast<int>(CoverageStatus::kPartial);

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
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
}

// C4: `SV_COV_START on a partially coverable scope reports `SV_COV_PARTIAL
// (Table 40-1, START/PARTIAL column) and still starts what it can.
TEST(CoverageControl, StartOnPartialScopeReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kPartial);

  EXPECT_EQ(RunControl(f, kStart, kScope), kPartial);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
}

// C4: `SV_COV_START on a scope with no coverage of the requested type reports
// `SV_COV_NOCOV (Table 40-1, START/NOCOV column) and starts nothing.
TEST(CoverageControl, StartOnUncoverableScopeReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kStart, kScope), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope)));
}

// C2/C4: `SV_COV_CHECK reports whether coverage can be obtained for each
// availability (Table 40-1, CHECK row: full -> OK, partial -> PARTIAL, none ->
// NOCOV) and never begins collecting.
TEST(CoverageControl, CheckReportsAvailabilityWithoutCollecting) {
  SimFixture f;
  Cov(f).SetAvailability("full", CoverageAvailability::kFull);
  Cov(f).SetAvailability("part", CoverageAvailability::kPartial);
  Cov(f).SetAvailability("none", CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kCheck, "full"), kOk);
  EXPECT_EQ(RunControl(f, kCheck, "part"), kPartial);
  EXPECT_EQ(RunControl(f, kCheck, "none"), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting("full"));
}

// C2/C4: `SV_COV_STOP halts an active collection and reports success.
TEST(CoverageControl, StopHaltsCollectionAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope)));
}

// C2/C4: `SV_COV_RESET clears collected coverage and reports success.
TEST(CoverageControl, ResetClearsCoverageAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 1U);
}

// C5 (shall): starting a scope whose coverage is already started has no effect.
// The redundant start does not advance the start transition count and still
// reports success.
TEST(CoverageControl, RepeatedStartHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope)));
  EXPECT_EQ(Cov(f).StartCount(std::string(kScope)), 1U);
}

// C6 (shall): repeated stops have no effect.
TEST(CoverageControl, RepeatedStopHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(Cov(f).StopCount(std::string(kScope)), 1U);
}

// C6 (shall): repeated resets have no effect; once coverage is cleared the
// second reset finds nothing to clear.
TEST(CoverageControl, RepeatedResetHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 1U);
}

// C2: a reset has no effect when no coverage is available, but still succeeds.
TEST(CoverageControl, ResetWithoutCoverageHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope)), 0U);
}

// C7: a scope the design does not contain is a bad argument; every control
// action over an unregistered scope reports `SV_COV_ERROR (Table 40-1, ERROR
// column) and fails without any effect.
TEST(CoverageControl, UnknownScopeIsBadArgument) {
  SimFixture f;
  const std::string kMissing = "$root.tb.nonesuch";

  EXPECT_EQ(RunControl(f, kStart, kMissing), kError);
  EXPECT_EQ(RunControl(f, kStop, kMissing), kError);
  EXPECT_EQ(RunControl(f, kReset, kMissing), kError);
  EXPECT_EQ(RunControl(f, kCheck, kMissing), kError);

  EXPECT_FALSE(Cov(f).IsRegistered(kMissing));
  EXPECT_FALSE(Cov(f).IsCollecting(kMissing));
}

// C7 (edge): a first argument outside the four §40.3.1 control constants is a
// bad argument, reported as `SV_COV_ERROR even on a fully coverable scope.
TEST(CoverageControl, InvalidControlConstantIsBadArgument) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), CoverageAvailability::kFull);

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

// §40.3.2.1 Table 40-2: what a call names is the scope plus, where the
// scope_def says so, the hierarchy below it. These cases drive the third
// argument rather than holding it at `SV_COV_HIER.
int RunControlWithScopeDef(SimFixture& f, int control, int scope_def,
                           std::string_view scope) {
  auto* call = MkSysCall(f.arena, "$coverage_control",
                         {MkInt(f.arena, static_cast<uint64_t>(control)),
                          MkInt(f.arena, 23 /* `SV_COV_TOGGLE */),
                          MkInt(f.arena, static_cast<uint64_t>(scope_def)),
                          MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

constexpr int kSvCovModule = 10;
constexpr int kSvCovHier = 11;

// §40.3.2.1 Table 40-2, the `SV_COV_HIER row: the control reaches "the named
// instance and any hierarchy below it", so starting collection over an instance
// starts it in the instances below that one as well.
TEST(CoverageControl, HierReachesTheHierarchyBelowTheNamedInstance) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.other", CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut"));
  EXPECT_TRUE(Cov(f).IsCollecting("top.dut.u1"));
  // An instance that is not below the named one is no part of the call.
  EXPECT_FALSE(Cov(f).IsCollecting("top.other"));
}

// §40.3.2.1 Table 40-2, the `SV_COV_MODULE row: the control reaches the named
// instance alone, "excluding any hierarchy in instances below that instance".
// The two scope definitions differ in exactly this, which the run below the
// instance is what shows.
TEST(CoverageControl, ModuleReachesTheNamedInstanceAlone) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut"));
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut.u1"));
}

// §40.3.2.1: "`SV_COV_PARTIAL, on a check or start operation, denotes that
// coverage is only partially available in the specified hierarchy." Over a
// hierarchy, that is what an instance below the named one offering no coverage
// makes of a start the named instance alone would have reported `SV_COV_OK for.
TEST(CoverageControl, APartlyCoverableHierarchyReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", CoverageAvailability::kNone);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);
}

// §40.3.2.1 Table 40-2, the definition-name column: a string that is not an
// instance path names a module definition, and the control then applies to "all
// instances of the given module" rather than to one. `SV_COV_MODULE excludes
// the hierarchy below each of those instances, which is what the child instance
// left uncollected here shows, and the status reported is of everything the
// call reached.
TEST(CoverageControl, ADefinitionNameControlsEveryInstanceOfThatModule) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2", "leaf");
  Cov(f).SetAvailability("top.u2.inner", CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2.inner", "other");

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "leaf"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.u1"));
  EXPECT_TRUE(Cov(f).IsCollecting("top.u2"));
  EXPECT_FALSE(Cov(f).IsCollecting("top.u2.inner"));
}

// §40.3.2.1: a hierarchy is partly available when any part of it is, and under
// a definition name the hierarchy is every instance of the module together. So
// one instance offering no coverage is what makes a start over all of them
// `SV_COV_PARTIAL, where the same start over the covered instance alone reports
// `SV_COV_OK.
TEST(CoverageControl, ADefinitionNameReportsTheStatusOfAllItsInstances) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", CoverageAvailability::kNone);
  Cov(f).SetModuleDefinition("top.u2", "leaf");

  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "leaf"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "top.u1"), kOk);
}

// §40.3.2.1: the scope definitions are the two the clause names, and a call
// that wrote something else wrote a bad argument - reported with `SV_COV_ERROR
// "on all operations ... typically due to errors in arguments" - rather than
// being taken for one of them.
TEST(CoverageControl, AnUnknownScopeDefinitionIsABadArgument) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, 99, "top.dut"), kError);
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut"));
}

}  // namespace
