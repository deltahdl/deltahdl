#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// Each test exercises the per-thread disable-protocol state, so start from a
// known-clean state. Clearing the disabled state also clears the per-episode
// acknowledgement.
void ResetDisableState() { DpiSetCurrentDisabledState(false); }

// §35.9 item a): when an exported task returns because a disable targets a
// parent in the mixed call chain, SystemVerilog guarantees it returns 1, and
// the calling import enters the disabled state.
TEST(DpiDisableProtocol, ExportedTaskReturnsOneWhenDisableTargetsAncestor) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  EXPECT_EQ(ret, 1);
  EXPECT_TRUE(rt.IsDisabledState());
}

// §35.9 item a): a task that does not return due to a disable returns 0 and
// leaves the calling import undisabled.
TEST(DpiDisableProtocol, ExportedTaskReturnsZeroWithoutDisable) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kNone);

  EXPECT_EQ(ret, 0);
  EXPECT_FALSE(rt.IsDisabledState());
}

// §35.9: if an exported task is itself the target of a disable, its parent
// import is not considered disabled when the task returns; the task returns 0
// and svIsDisabledState() reports 0 as well.
TEST(DpiDisableProtocol,
     ExportedTaskTargetedItselfReturnsZeroAndParentNotDisabled) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kExportItself);

  EXPECT_EQ(ret, 0);
  EXPECT_FALSE(rt.IsDisabledState());
  EXPECT_EQ(svIsDisabledState(), 0);
}

// §35.9: a subroutine determines that it is in the disabled state by calling
// svIsDisabledState(). After a disable propagates through an export into the
// calling import, the named API function reports the disabled state; once the
// state is left it reports 0 again.
TEST(DpiDisableProtocol, SvIsDisabledStateReflectsCurrentState) {
  ResetDisableState();
  DpiRuntime rt;

  EXPECT_EQ(svIsDisabledState(), 0);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  EXPECT_EQ(svIsDisabledState(), 1);

  DpiSetCurrentDisabledState(false);
  EXPECT_EQ(svIsDisabledState(), 0);
}

// §35.9 item d): once an imported subroutine has entered the disabled state, it
// is illegal for the current call to make any further calls to exported
// subroutines. The runtime rejects such a call and does not run the export.
TEST(DpiDisableProtocol, DisabledImportCannotCallExport) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_export";
  exp.sv_name = "sv_export";
  bool ran = false;
  exp.impl = [&ran](const std::vector<DpiArgValue>&) {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_import", sc, /*is_task=*/true);

  // The import enters the disabled state, then tries to call an export.
  DpiSetCurrentDisabledState(true);
  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kDisabledStateExportCall);
  EXPECT_FALSE(ran);
}

// §35.9 item d) is gated on the disabled state alone: a context import that is
// not in the disabled state may still call the export as the earlier clauses
// permit, confirming the new check does not reject ordinary calls.
TEST(DpiDisableProtocol, UndisabledImportMayStillCallExport) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_export";
  exp.sv_name = "sv_export";
  bool ran = false;
  exp.impl = [&ran](const std::vector<DpiArgValue>&) {
    ran = true;
    return DpiArgValue::FromInt(7);
  };
  rt.RegisterExport(exp);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_import", sc, /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

// §35.9 item b): a simulator shall check that an imported task returning due to
// a disable returns 1. Returning 1 satisfies the check; returning anything else
// is a protocol violation the simulator turns into a fatal error.
TEST(DpiDisableProtocol, ImportedTaskMustReturnOneWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(/*is_task=*/true,
                                                      /*task_return_value=*/1));
  EXPECT_FALSE(
      rt.CheckImportedSubroutineDisableReturn(/*is_task=*/true,
                                              /*task_return_value=*/0));
}

// §35.9 item c): a simulator shall check that an imported function returning
// due to a disable called svAckDisabledState() first. Acknowledging satisfies
// the check; failing to acknowledge is a protocol violation.
TEST(DpiDisableProtocol, ImportedFunctionMustAcknowledgeWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  // Without an acknowledgement the function-return check fails.
  EXPECT_FALSE(
      rt.CheckImportedSubroutineDisableReturn(/*is_task=*/false,
                                              /*task_return_value=*/0));

  // After the function acknowledges via the named API, the check passes.
  svAckDisabledState();
  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(/*is_task=*/false,
                                                      /*task_return_value=*/0));
  EXPECT_TRUE(DpiCurrentDisableAcknowledged());
}

// §35.9: the verification only applies while a disable is in effect. With no
// disable there is nothing to check, so the protocol check passes for any
// return value and without an acknowledgement.
TEST(DpiDisableProtocol, ProtocolCheckIsTrivialWithoutDisable) {
  ResetDisableState();
  DpiRuntime rt;

  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(/*is_task=*/true,
                                                      /*task_return_value=*/0));
  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(/*is_task=*/false,
                                                      /*task_return_value=*/0));
}

// §35.9: the per-episode acknowledgement is cleared when the disabled state is
// left, so an unrelated later episode starts unacknowledged.
TEST(DpiDisableProtocol, AcknowledgementClearedWhenLeavingDisabledState) {
  ResetDisableState();
  DpiSetCurrentDisabledState(true);
  svAckDisabledState();
  EXPECT_TRUE(DpiCurrentDisableAcknowledged());

  DpiSetCurrentDisabledState(false);
  EXPECT_FALSE(DpiCurrentDisableAcknowledged());
}

// §35.9: when an imported subroutine returns due to a disable, the values of
// its output and inout parameters are undefined, and a simulator is not
// obligated to propagate anything the foreign code wrote. The runtime exercises
// that latitude: with a disable in effect, the output/inout actuals are left
// unchanged and the result is an undetermined value.
TEST(DpiDisableProtocol, OutputAndInoutNotPropagatedWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_io";
  func.sv_name = "io";
  func.return_type = DataTypeKind::kInt;
  func.args = {
      DpiArg{"o", DataTypeKind::kInt, Direction::kOutput},
      DpiArg{"io", DataTypeKind::kInt, Direction::kInout},
  };
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(222);
    a[1] = DpiArgValue::FromInt(333);
    return DpiArgValue::FromInt(444);
  };
  rt.RegisterImport(std::move(func));

  // Without a disable, the writes propagate and the result is returned.
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10),
                                      DpiArgValue::FromInt(20)};
  DpiArgValue result = rt.CallImportWithArgs("io", actuals);
  EXPECT_EQ(result.AsInt(), 444);
  EXPECT_EQ(actuals[0].AsInt(), 222);
  EXPECT_EQ(actuals[1].AsInt(), 333);

  // With a disable in effect, nothing the foreign code wrote is propagated: the
  // actuals keep their pre-call values and an undetermined result is yielded.
  DpiSetCurrentDisabledState(true);
  std::vector<DpiArgValue> disabled_actuals = {DpiArgValue::FromInt(10),
                                               DpiArgValue::FromInt(20)};
  DpiArgValue disabled_result = rt.CallImportWithArgs("io", disabled_actuals);
  EXPECT_EQ(disabled_result.AsInt(), 0);
  EXPECT_EQ(disabled_actuals[0].AsInt(), 10);
  EXPECT_EQ(disabled_actuals[1].AsInt(), 20);

  ResetDisableState();
}

// §35.9 item d): the prohibition applies to any imported subroutine in the
// disabled state, whatever it tries to call. A disabled *function* import
// calling an exported *task* is rejected on the disabled-state ground — the
// disabled-state illegality holds independently of the §35.8 function-calls-
// task prohibition that would also forbid it.
TEST(DpiDisableProtocol, DisabledFunctionImportCannotCallExportedTask) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  bool ran = false;
  task_export.impl = [&ran](const std::vector<DpiArgValue>&) {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  // A context *function* import (is_task = false) opens the chain.
  rt.EnterContextImportCall("ctx_func_import", sc, /*is_task=*/false);

  DpiSetCurrentDisabledState(true);
  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kDisabledStateExportCall);
  EXPECT_FALSE(ran);
  ResetDisableState();
}

// §35.9 item d): the prohibition does not depend on the chain's context
// property either. A disabled *noncontext* import calling an export is rejected
// on the disabled-state ground — even though §35.5.3 would independently forbid
// a noncontext import from reaching an export.
TEST(DpiDisableProtocol, DisabledNoncontextImportCannotCallExport) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_export";
  exp.sv_name = "sv_export";
  bool ran = false;
  exp.impl = [&ran](const std::vector<DpiArgValue>&) {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);

  rt.EnterNoncontextImportCall("nonctx_import");

  DpiSetCurrentDisabledState(true);
  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kDisabledStateExportCall);
  EXPECT_FALSE(ran);
  ResetDisableState();
}

// §35.9 item b): an imported task that returns due to a disable shall return 1.
// Any other value — not only 0 — is a protocol violation. A task returning 2
// while a disable is in effect fails the simulator's check.
TEST(DpiDisableProtocol,
     ImportedTaskReturnOtherThanOneWhenDisabledIsViolation) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  EXPECT_FALSE(
      rt.CheckImportedSubroutineDisableReturn(/*is_task=*/true,
                                              /*task_return_value=*/2));
  ResetDisableState();
}

// §35.9: the undetermined result yielded when a disable is in effect is correct
// for the formal return type, not forced to an int. A real-returning import
// called under a disable yields a real undetermined value (0.0) and still does
// not propagate the foreign code's output write.
TEST(DpiDisableProtocol, UndeterminedResultIsReturnTypeCorrectWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_rfn";
  func.sv_name = "rfn";
  func.return_type = DataTypeKind::kReal;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(777);
    return DpiArgValue::FromReal(3.5);
  };
  rt.RegisterImport(std::move(func));

  DpiSetCurrentDisabledState(true);
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(11)};
  DpiArgValue result = rt.CallImportWithArgs("rfn", actuals);

  // The result is an undetermined real, not an int, and the output write is
  // not propagated back to the caller.
  EXPECT_EQ(result.type, DataTypeKind::kReal);
  EXPECT_DOUBLE_EQ(result.AsReal(), 0.0);
  EXPECT_EQ(actuals[0].AsInt(), 11);
  ResetDisableState();
}

// §35.9: an imported subroutine is in the disabled state while a disable
// "somewhere in the design targets either it or a parent". Once the chain the
// disable was propagating through has unwound, nothing targets anything, so the
// episode is over and svIsDisabledState() reports 0 to foreign code running
// outside any import call.
TEST(DpiDisableProtocol, DisabledStateEndsWhenTheImportChainUnwinds) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("outer", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  ASSERT_TRUE(rt.IsDisabledState());
  rt.LeaveImportCall();

  EXPECT_EQ(svIsDisabledState(), 0);
}

// The episode ends with the chain and not with any frame in it: an inner frame
// popping while an outer one is still open leaves the disable propagating,
// which is what item b) has the outer import acknowledge by its return value.
TEST(DpiDisableProtocol, DisabledStateSurvivesAnInnerFrameLeavingTheChain) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("outer", /*is_task=*/true);
  rt.EnterNoncontextImportCall("inner", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  rt.LeaveImportCall();

  EXPECT_TRUE(rt.IsDisabledState());
  rt.LeaveImportCall();
  ResetDisableState();
}

// §35.9 licenses a simulator to drop an output or inout argument only "if a
// disable is in effect". A call made after the disabled chain unwound has none
// in effect, so its arguments are propagated as any undisabled call's are. This
// is what the leaked state cost: the licence was taken where it did not apply.
TEST(DpiDisableProtocol, ACallAfterADisabledChainPropagatesItsOutputArgument) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_io";
  func.sv_name = "io";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(222);
    return DpiArgValue::FromInt(444);
  };
  rt.RegisterImport(std::move(func));

  rt.EnterNoncontextImportCall("outer", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  rt.LeaveImportCall();

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10)};
  DpiArgValue result = rt.CallImportWithArgs("io", actuals);

  EXPECT_EQ(actuals[0].AsInt(), 222);
  EXPECT_EQ(result.AsInt(), 444);
}

// §35.9 item b): an imported task returning due to a disable shall return 1.
// Returning 0 is the violation the clause has a simulator check, and "if any
// protocol item is not correctly followed, a fatal simulation error is issued".
TEST(DpiDisableProtocol, ImportedTaskReturningZeroUnderADisableIsFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  bool ok = rt.VerifyImportReturnUnderDisable(/*task_return_value=*/0);
  testing::internal::GetCapturedStderr();

  EXPECT_FALSE(ok);
  EXPECT_TRUE(rt.DisableProtocolFatalErrorIssued());
  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item b)"),
            std::string::npos);
  ResetDisableState();
}

// §35.9 item b) is followed when the imported task returns 1, so no fatal
// simulation error is issued and the run continues.
TEST(DpiDisableProtocol, ImportedTaskReturningOneUnderADisableIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  EXPECT_TRUE(rt.VerifyImportReturnUnderDisable(/*task_return_value=*/1));
  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  ResetDisableState();
}

// §35.9 item c): an imported function returning due to a disable shall call
// svAckDisabledState() first. The return is the frame leaving the call chain,
// so the check is made there and needs nothing from the caller.
TEST(DpiDisableProtocol, ImportedFunctionReturningUnacknowledgedIsFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_func", /*is_task=*/false);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.LeaveImportCall();
  testing::internal::GetCapturedStderr();

  EXPECT_TRUE(rt.DisableProtocolFatalErrorIssued());
  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item c)"),
            std::string::npos);
  ResetDisableState();
}

// §35.9 item c) is followed when the imported function acknowledges the disable
// before it returns, so its return issues no fatal simulation error.
TEST(DpiDisableProtocol, ImportedFunctionThatAcknowledgedIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_func", /*is_task=*/false);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  svAckDisabledState();
  rt.LeaveImportCall();

  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  ResetDisableState();
}

// §35.9 item d): an imported subroutine in the disabled state making a further
// call to an exported subroutine is a violation, and the clause has the
// simulator issue a fatal simulation error for it rather than only refuse the
// call.
TEST(DpiDisableProtocol, ExportCallFromADisabledImportIsFatal) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_export";
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_import", sc, /*is_task=*/false);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  DpiArgValue result;
  rt.CallExportFromImport("sv_export", {}, &result);
  testing::internal::GetCapturedStderr();

  EXPECT_TRUE(rt.DisableProtocolFatalErrorIssued());
  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item d)"),
            std::string::npos);
  ResetDisableState();
}

// §35.9 requires the violation to be issued as a fatal simulation error rather
// than only recorded, so it is written to the stream and under the severity
// word §20.10 gives $fatal.
TEST(DpiDisableProtocol, TheDisableProtocolFatalErrorReachesTheErrorStream) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.VerifyImportReturnUnderDisable(/*task_return_value=*/0);
  std::string err = testing::internal::GetCapturedStderr();

  EXPECT_NE(err.find("FATAL: 35.9 item b)"), std::string::npos);
  ResetDisableState();
}

// §35.9's checks apply to a subroutine returning while a disable is in effect.
// An imported task returning with none in effect returns whatever it returns,
// so nothing is verified and no fatal simulation error is issued.
TEST(DpiDisableProtocol, AReturnWithNoDisableInEffectIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", /*is_task=*/true);

  EXPECT_TRUE(rt.VerifyImportReturnUnderDisable(/*task_return_value=*/0));
  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  rt.LeaveImportCall();
  ResetDisableState();
}

// A fatal simulation error ends the run, so the error this runtime reports is
// the first violation. A second one is reached only because nothing here can
// halt the caller, and it does not displace the error that ended the run.
TEST(DpiDisableProtocol, TheFirstDisableProtocolViolationIsTheRecordedError) {
  ResetDisableState();
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_export";
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_import", sc, /*is_task=*/true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.VerifyImportReturnUnderDisable(/*task_return_value=*/0);
  DpiArgValue result;
  rt.CallExportFromImport("sv_export", {}, &result);
  std::string err = testing::internal::GetCapturedStderr();

  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item b)"),
            std::string::npos);
  EXPECT_EQ(err.find("35.9 item d)"), std::string::npos);
  ResetDisableState();
}

// ---------------------------------------------------------------------------
// The same protocol, asked of a call a design makes.
//
// The cases above open and leave the import frame themselves. A call written in
// SystemVerilog opens one through EvalDpiCall in
// src/simulator/eval_function_dpi.cpp, which is where §35.9's "a fatal
// simulation error is issued" has to be reached from if a design's imports are
// checked at all.
// ---------------------------------------------------------------------------

// A design calling an imported function whose foreign body enters the disabled
// state, as a disable somewhere in the design targeting the call would put it
// there, and returns having acknowledged it or not.
struct AnImportDisabledInADesign {
  DpiRuntime rt;
  SimFixture f;

  explicit AnImportDisabledInADesign(bool acknowledge) {
    ResetDisableState();
    DpiRtFunction func;
    func.c_name = "c_wander";
    func.sv_name = "wander";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"v", DataTypeKind::kInt, Direction::kInput}};
    func.impl = [acknowledge](const std::vector<DpiArgValue>&) {
      DpiSetCurrentDisabledState(true);
      if (acknowledge) DpiAckCurrentDisable();
      return DpiArgValue::FromInt(0);
    };
    rt.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&rt);
    // Leaving the import call ends the chain the disable was propagating
    // through, so the thread-local state is clear again by the time the case
    // reads what the check recorded.
    EvalFunctionCall(ParseExprFrom("wander(1)", f), f.ctx, f.arena);
  }
};

// §35.9 item c): "An imported function that returns while a disable is in
// effect shall call svAckDisabledState() before returning", and "if any
// protocol item is not correctly followed, a fatal simulation error is issued".
// The body returns without acknowledging, and the design's call site is where
// the check has to happen.
TEST(DpiDisableInADesign,
     AnImportReturningWithoutAcknowledgingADisableIsFatal) {
  AnImportDisabledInADesign run(/*acknowledge=*/false);
  EXPECT_TRUE(run.rt.DisableProtocolFatalErrorIssued());
}

// The error names item c) and the import that breached it, so a run stopping on
// it says which subroutine to look at rather than only that something was
// wrong.
TEST(DpiDisableInADesign, TheFatalErrorNamesTheImportThatBreachedItemC) {
  AnImportDisabledInADesign run(/*acknowledge=*/false);
  EXPECT_NE(run.rt.DisableProtocolFatalError().find("wander"),
            std::string::npos);
  EXPECT_NE(run.rt.DisableProtocolFatalError().find("35.9 item c)"),
            std::string::npos);
}

// The other side of item c): a body that does acknowledge the disable before
// returning has followed the protocol, so no error is issued. Without this the
// case above would hold of a design that called every import's return a
// breach.
TEST(DpiDisableInADesign, AnImportThatAcknowledgedTheDisableIsNotFatal) {
  AnImportDisabledInADesign run(/*acknowledge=*/true);
  EXPECT_FALSE(run.rt.DisableProtocolFatalErrorIssued());
}

}  // namespace
