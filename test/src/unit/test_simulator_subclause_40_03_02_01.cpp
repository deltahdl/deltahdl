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
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §40.3.1 control constants (first argument).
constexpr int kStart = 0;
constexpr int kStop = 1;
constexpr int kReset = 2;
constexpr int kCheck = 3;

// §40.3.1 `SV_COV_TOGGLE, the coverage type the calls below control.
constexpr int kToggle = 23;

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
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
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
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

// C4: `SV_COV_START on a partially coverable scope reports `SV_COV_PARTIAL
// (Table 40-1, START/PARTIAL column) and still starts what it can.
TEST(CoverageControl, StartOnPartialScopeReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kPartial);

  EXPECT_EQ(RunControl(f, kStart, kScope), kPartial);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

// C4: `SV_COV_START on a scope with no coverage of the requested type reports
// `SV_COV_NOCOV (Table 40-1, START/NOCOV column) and starts nothing.
TEST(CoverageControl, StartOnUncoverableScopeReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kStart, kScope), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

// C2/C4: `SV_COV_CHECK reports whether coverage can be obtained for each
// availability (Table 40-1, CHECK row: full -> OK, partial -> PARTIAL, none ->
// NOCOV) and never begins collecting.
TEST(CoverageControl, CheckReportsAvailabilityWithoutCollecting) {
  SimFixture f;
  Cov(f).SetAvailability("full", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("part", kToggle, CoverageAvailability::kPartial);
  Cov(f).SetAvailability("none", kToggle, CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kCheck, "full"), kOk);
  EXPECT_EQ(RunControl(f, kCheck, "part"), kPartial);
  EXPECT_EQ(RunControl(f, kCheck, "none"), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting("full", kToggle));
}

// C2/C4: `SV_COV_STOP halts an active collection and reports success.
TEST(CoverageControl, StopHaltsCollectionAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

// C2/C4: `SV_COV_RESET clears collected coverage and reports success.
TEST(CoverageControl, ResetClearsCoverageAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 1U);
}

// C5 (shall): starting a scope whose coverage is already started has no effect.
// The redundant start does not advance the start transition count and still
// reports success.
TEST(CoverageControl, RepeatedStartHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
  EXPECT_EQ(Cov(f).StartCount(std::string(kScope), kToggle), 1U);
}

// C6 (shall): repeated stops have no effect.
TEST(CoverageControl, RepeatedStopHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(Cov(f).StopCount(std::string(kScope), kToggle), 1U);
}

// C6 (shall): repeated resets have no effect; once coverage is cleared the
// second reset finds nothing to clear.
TEST(CoverageControl, RepeatedResetHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 1U);
}

// C2: a reset has no effect when no coverage is available, but still succeeds.
TEST(CoverageControl, ResetWithoutCoverageHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 0U);
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
  EXPECT_FALSE(Cov(f).IsCollecting(kMissing, kToggle));
}

// C7 (edge): a first argument outside the four §40.3.1 control constants is a
// bad argument, reported as `SV_COV_ERROR even on a fully coverable scope.
TEST(CoverageControl, InvalidControlConstantIsBadArgument) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, 99, kScope), kError);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
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
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
       MkInt(f.arena, static_cast<uint64_t>(scope_def)),
       MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

constexpr int kSvCovModule = 10;
constexpr int kSvCovHier = 11;

// §40.3.2.1 Table 40-2, the `SV_COV_HIER row: the control reaches the named
// instance and everything beneath it in the hierarchy, so starting collection
// over an instance starts it in the instances below that one as well.
TEST(CoverageControl, HierReachesTheHierarchyBelowTheNamedInstance) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.other", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut", kToggle));
  EXPECT_TRUE(Cov(f).IsCollecting("top.dut.u1", kToggle));
  // An instance that is not below the named one is no part of the call.
  EXPECT_FALSE(Cov(f).IsCollecting("top.other", kToggle));
}

// §40.3.2.1 Table 40-2, the `SV_COV_MODULE row: the control reaches the named
// instance alone, leaving out the instances beneath it. The two scope
// definitions differ in exactly this, which the run below the instance is what
// shows.
TEST(CoverageControl, ModuleReachesTheNamedInstanceAlone) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut", kToggle));
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut.u1", kToggle));
}

// §40.3.2.1: a check or start that answers `SV_COV_PARTIAL says some, but not
// all, of the named hierarchy offers coverage. Over a hierarchy, that is what
// an instance below the named one offering no coverage makes of a start the
// named instance alone would have reported `SV_COV_OK for.
TEST(CoverageControl, APartlyCoverableHierarchyReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kNone);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);
}

// §40.3.2.1 Table 40-2, the definition-name column: a string that is not an
// instance path names a module definition, and the control then applies to
// every instance of that module rather than to one. `SV_COV_MODULE excludes the
// hierarchy below each of those instances, which is what the child instance
// left uncollected here shows, and the status reported is of everything the
// call reached.
TEST(CoverageControl, ADefinitionNameControlsEveryInstanceOfThatModule) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2", "leaf");
  Cov(f).SetAvailability("top.u2.inner", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2.inner", "other");

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "leaf"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.u1", kToggle));
  EXPECT_TRUE(Cov(f).IsCollecting("top.u2", kToggle));
  EXPECT_FALSE(Cov(f).IsCollecting("top.u2.inner", kToggle));
}

// §40.3.2.1: a hierarchy is partly available when any part of it is, and under
// a definition name the hierarchy is every instance of the module together. So
// one instance offering no coverage is what makes a start over all of them
// `SV_COV_PARTIAL, where the same start over the covered instance alone reports
// `SV_COV_OK.
TEST(CoverageControl, ADefinitionNameReportsTheStatusOfAllItsInstances) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", kToggle, CoverageAvailability::kNone);
  Cov(f).SetModuleDefinition("top.u2", "leaf");

  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "leaf"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "top.u1"), kOk);
}

// §40.3.2.1: the scope definitions are the two the clause names, and a call
// that wrote something else wrote a bad argument - reported with `SV_COV_ERROR,
// which any operation can answer and which a wrong argument is the usual cause
// of - rather than being taken for one of them.
TEST(CoverageControl, AnUnknownScopeDefinitionIsABadArgument) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, 99, "top.dut"), kError);
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut", kToggle));
}

// A design with FSM state coverage in two instances: `top` holds an FSM of two
// legal states and its child `u1`, an instance of `leaf`, one of three. The
// §40.3.1 constants are written as their values: `SV_COV_CHECK 3,
// `SV_COV_MODULE 10, `SV_COV_HIER 11 and `SV_COV_FSM_STATE 21. `body` is
// what `top` runs once both FSMs stand in a legal state, setting r1 to r3.
std::string TwoFsmDesign(const std::string& body) {
  return "module leaf;\n"
         "  parameter [1:0] /* tool enum leaf_e */ A = 0, B = 1, C = 2;\n"
         "  /* tool state_vector st enum leaf_e */\n"
         "  logic [1:0] st;\n"
         "  initial st = A;\n"
         "endmodule\n"
         "module top;\n"
         "  parameter [1:0] /* tool enum top_e */ X = 0, Y = 1;\n"
         "  /* tool state_vector ts enum top_e */\n"
         "  logic [1:0] ts;\n"
         "  leaf u1();\n"
         "  string m;\n"
         "  int r1, r2, r3;\n"
         "  initial begin\n"
         "    ts = X; #1\n" +
         body +
         "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
         "  end\n"
         "endmodule\n";
}

// §40.3.2.1 Table 40-2: an instance is named by its hierarchical path, and a
// path headed by $root is read from the top of the design. The instance alone
// holds two coverable states, the instance with its child five, and the child
// three - none of them the `SV_COV_ERROR an unread argument gave (#7523).
TEST(CoverageControl, AnInstanceIsNamedByARootedHierarchicalPath) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign("    r1 = $coverage_get_max(21, 10, $root.top);\n"
                   "    r2 = $coverage_get_max(21, 11, $root.top);\n"
                   "    r3 = $coverage_get_max(21, 11, $root.top.u1);\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "2 5 3\n");
}

// Table 40-2's note: a path follows the ordinary hierarchical name rules, so an
// instance of the calling scope is named without a dot, and a path written
// from the top is found from below it as §23.8 searches upward (#7523).
TEST(CoverageControl, AnInstanceOfTheCallingScopeNeedsNoDot) {
  SimFixture f;
  const std::string kOut =
      RunCapture(TwoFsmDesign("    r1 = $coverage_get_max(21, 11, u1);\n"
                              "    r2 = $coverage_get_max(21, 11, top.u1);\n"
                              "    r3 = $coverage_control(3, 21, 10, u1);\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "3 3 1\n");
}

// Figure 40-1's examples pass $root itself, the root above every top-level
// instance, so a hierarchical check covers the whole design - both FSMs here,
// for `SV_COV_OK - and a hierarchical maximum sums all five states (#7523).
TEST(CoverageControl, RootAloneNamesTheWholeDesign) {
  SimFixture f;
  const std::string kOut =
      RunCapture(TwoFsmDesign("    r1 = $coverage_control(3, 21, 11, $root);\n"
                              "    r2 = $coverage_get_max(21, 11, $root);\n"
                              "    r3 = $coverage_get(21, 11, $root);\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 5 2\n");
}

// §40.3.2.1: a module definition name is a string, and a string variable is
// one as much as a literal is, so the name it holds is the definition read:
// `leaf`, three states, and `top` by its path, available in full, whatever
// expression gives the string (#7524).
TEST(CoverageControl, AStringVariableNamesWhatItHolds) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign(
          "    m = \"leaf\";\n"
          "    r1 = $coverage_get_max(21, 11, m);\n"
          "    r2 = $coverage_get(21, 11, m);\n"
          "    m = \"top\";\n"
          "    r3 = $coverage_control(3, 21, 10, $sformatf(\"%s\", m));\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "3 1 1\n");
}

// §40.3.2.1: a control acts on the coverage type its call names. A design
// holding no assertion offers no assertion coverage, whatever FSM coverage it
// has, so a check of that type answers `SV_COV_NOCOV (0); and stopping
// statement coverage leaves FSM state coverage collecting, so the state the
// FSM reaches afterwards still counts (#7525).
TEST(CoverageControl, AControlActsOnTheCoverageTypeItNames) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign("    r1 = $coverage_control(3, 20, 10, \"top\");\n"
                   "    r2 = $coverage_control(1, 22, 11, \"top\");\n"
                   "    ts = Y; #1\n"
                   "    r3 = $coverage_get(21, 10, \"top\");\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "0 1 2\n");
}

// Table 40-2: a path headed by $root is read from the top of the design alone,
// so one naming no instance there names nothing, a bad argument, and so does a
// call that left the scope out (#7523).
TEST(CoverageControl, ARootedPathNamingNoInstanceIsABadArgument) {
  SimFixture f;
  Cov(f).SetModuleDefinition("top", "top");
  Cov(f).SetAvailability("top", kToggle, CoverageAvailability::kFull);
  Expr* nosuch = MkId(f.arena, "nosuch");
  nosuch->scope_prefix = "$root";
  auto run = [&f](Expr* scope) {
    auto* call = MkSysCall(f.arena, "$coverage_control",
                           {MkInt(f.arena, kCheck), MkInt(f.arena, kToggle),
                            MkInt(f.arena, 11 /* `SV_COV_HIER */), scope});
    return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
  };

  EXPECT_EQ(run(nosuch), kError);
  EXPECT_EQ(run(nullptr), kError);
}

}  // namespace
