#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

void ResetDisableState() { DpiSetCurrentDisabledState(false); }

TEST(DpiDisableProtocol, ExportedTaskReturnsOneWhenDisableTargetsAncestor) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  EXPECT_EQ(ret, 1);
  EXPECT_TRUE(rt.IsDisabledState());
}

TEST(DpiDisableProtocol, ExportedTaskReturnsZeroWithoutDisable) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kNone);

  EXPECT_EQ(ret, 0);
  EXPECT_FALSE(rt.IsDisabledState());
}

TEST(DpiDisableProtocol,
     ExportedTaskTargetedItselfReturnsZeroAndParentNotDisabled) {
  ResetDisableState();
  DpiRuntime rt;

  int ret = rt.ReturnFromExportUnderDisable(DpiDisableTarget::kExportItself);

  EXPECT_EQ(ret, 0);
  EXPECT_FALSE(rt.IsDisabledState());
  EXPECT_EQ(svIsDisabledState(), 0);
}

TEST(DpiDisableProtocol, SvIsDisabledStateReflectsCurrentState) {
  ResetDisableState();
  DpiRuntime rt;

  EXPECT_EQ(svIsDisabledState(), 0);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  EXPECT_EQ(svIsDisabledState(), 1);

  DpiSetCurrentDisabledState(false);
  EXPECT_EQ(svIsDisabledState(), 0);
}

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
  rt.EnterContextImportCall("ctx_import", sc, true);

  DpiSetCurrentDisabledState(true);
  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kDisabledStateExportCall);
  EXPECT_FALSE(ran);
}

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
  rt.EnterContextImportCall("ctx_import", sc, true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

TEST(DpiDisableProtocol, ImportedTaskMustReturnOneWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(true, 1));
  EXPECT_FALSE(rt.CheckImportedSubroutineDisableReturn(true, 0));
}

TEST(DpiDisableProtocol, ImportedFunctionMustAcknowledgeWhenDisabled) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  EXPECT_FALSE(rt.CheckImportedSubroutineDisableReturn(false, 0));

  svAckDisabledState();
  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(false, 0));
  EXPECT_TRUE(DpiCurrentDisableAcknowledged());
}

TEST(DpiDisableProtocol, ProtocolCheckIsTrivialWithoutDisable) {
  ResetDisableState();
  DpiRuntime rt;

  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(true, 0));
  EXPECT_TRUE(rt.CheckImportedSubroutineDisableReturn(false, 0));
}

TEST(DpiDisableProtocol, AcknowledgementClearedWhenLeavingDisabledState) {
  ResetDisableState();
  DpiSetCurrentDisabledState(true);
  svAckDisabledState();
  EXPECT_TRUE(DpiCurrentDisableAcknowledged());

  DpiSetCurrentDisabledState(false);
  EXPECT_FALSE(DpiCurrentDisableAcknowledged());
}

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

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10),
                                      DpiArgValue::FromInt(20)};
  DpiArgValue result = rt.CallImportWithArgs("io", actuals);
  EXPECT_EQ(result.AsInt(), 444);
  EXPECT_EQ(actuals[0].AsInt(), 222);
  EXPECT_EQ(actuals[1].AsInt(), 333);

  DpiSetCurrentDisabledState(true);
  std::vector<DpiArgValue> disabled_actuals = {DpiArgValue::FromInt(10),
                                               DpiArgValue::FromInt(20)};
  DpiArgValue disabled_result = rt.CallImportWithArgs("io", disabled_actuals);
  EXPECT_EQ(disabled_result.AsInt(), 0);
  EXPECT_EQ(disabled_actuals[0].AsInt(), 10);
  EXPECT_EQ(disabled_actuals[1].AsInt(), 20);

  ResetDisableState();
}

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
  rt.EnterContextImportCall("ctx_func_import", sc, false);

  DpiSetCurrentDisabledState(true);
  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);

  EXPECT_EQ(status, DpiExportCallStatus::kDisabledStateExportCall);
  EXPECT_FALSE(ran);
  ResetDisableState();
}

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

TEST(DpiDisableProtocol,
     ImportedTaskReturnOtherThanOneWhenDisabledIsViolation) {
  ResetDisableState();
  DpiRuntime rt;
  DpiSetCurrentDisabledState(true);

  EXPECT_FALSE(rt.CheckImportedSubroutineDisableReturn(true, 2));
  ResetDisableState();
}

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

  EXPECT_EQ(result.type, DataTypeKind::kReal);
  EXPECT_DOUBLE_EQ(result.AsReal(), 0.0);
  EXPECT_EQ(actuals[0].AsInt(), 11);
  ResetDisableState();
}

TEST(DpiDisableProtocol, DisabledStateEndsWhenTheImportChainUnwinds) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("outer", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  ASSERT_TRUE(rt.IsDisabledState());
  rt.LeaveImportCall();

  EXPECT_EQ(svIsDisabledState(), 0);
}

TEST(DpiDisableProtocol, DisabledStateSurvivesAnInnerFrameLeavingTheChain) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("outer", true);
  rt.EnterNoncontextImportCall("inner", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  rt.LeaveImportCall();

  EXPECT_TRUE(rt.IsDisabledState());
  rt.LeaveImportCall();
  ResetDisableState();
}

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

  rt.EnterNoncontextImportCall("outer", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  rt.LeaveImportCall();

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10)};
  DpiArgValue result = rt.CallImportWithArgs("io", actuals);

  EXPECT_EQ(actuals[0].AsInt(), 222);
  EXPECT_EQ(result.AsInt(), 444);
}

TEST(DpiDisableProtocol, ImportedTaskReturningZeroUnderADisableIsFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  bool ok = rt.VerifyImportReturnUnderDisable(0);
  testing::internal::GetCapturedStderr();

  EXPECT_FALSE(ok);
  EXPECT_TRUE(rt.DisableProtocolFatalErrorIssued());
  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item b)"),
            std::string::npos);
  ResetDisableState();
}

TEST(DpiDisableProtocol, ImportedTaskReturningOneUnderADisableIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  EXPECT_TRUE(rt.VerifyImportReturnUnderDisable(1));
  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  ResetDisableState();
}

TEST(DpiDisableProtocol, ImportedFunctionReturningUnacknowledgedIsFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_func", false);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.LeaveImportCall();
  testing::internal::GetCapturedStderr();

  EXPECT_TRUE(rt.DisableProtocolFatalErrorIssued());
  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item c)"),
            std::string::npos);
  ResetDisableState();
}

TEST(DpiDisableProtocol, ImportedFunctionThatAcknowledgedIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_func", false);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
  svAckDisabledState();
  rt.LeaveImportCall();

  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  ResetDisableState();
}

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
  rt.EnterContextImportCall("ctx_import", sc, false);
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

TEST(DpiDisableProtocol, TheDisableProtocolFatalErrorReachesTheErrorStream) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.VerifyImportReturnUnderDisable(0);
  std::string err = testing::internal::GetCapturedStderr();

  EXPECT_NE(err.find("FATAL: 35.9 item b)"), std::string::npos);
  ResetDisableState();
}

TEST(DpiDisableProtocol, AReturnWithNoDisableInEffectIsNotFatal) {
  ResetDisableState();
  DpiRuntime rt;

  rt.EnterNoncontextImportCall("imp_task", true);

  EXPECT_TRUE(rt.VerifyImportReturnUnderDisable(0));
  EXPECT_FALSE(rt.DisableProtocolFatalErrorIssued());
  rt.LeaveImportCall();
  ResetDisableState();
}

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
  rt.EnterContextImportCall("ctx_import", sc, true);
  rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);

  testing::internal::CaptureStderr();
  rt.VerifyImportReturnUnderDisable(0);
  DpiArgValue result;
  rt.CallExportFromImport("sv_export", {}, &result);
  std::string err = testing::internal::GetCapturedStderr();

  EXPECT_NE(rt.DisableProtocolFatalError().find("35.9 item b)"),
            std::string::npos);
  EXPECT_EQ(err.find("35.9 item d)"), std::string::npos);
  ResetDisableState();
}

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
    EvalFunctionCall(ParseExprFrom("wander(1)", f), f.ctx, f.arena);
  }
};

TEST(DpiDisableInADesign,
     AnImportReturningWithoutAcknowledgingADisableIsFatal) {
  AnImportDisabledInADesign run(false);
  EXPECT_TRUE(run.rt.DisableProtocolFatalErrorIssued());
}

TEST(DpiDisableInADesign, TheFatalErrorNamesTheImportThatBreachedItemC) {
  AnImportDisabledInADesign run(false);
  EXPECT_NE(run.rt.DisableProtocolFatalError().find("wander"),
            std::string::npos);
  EXPECT_NE(run.rt.DisableProtocolFatalError().find("35.9 item c)"),
            std::string::npos);
}

TEST(DpiDisableInADesign, AnImportThatAcknowledgedTheDisableIsNotFatal) {
  AnImportDisabledInADesign run(true);
  EXPECT_FALSE(run.rt.DisableProtocolFatalErrorIssued());
}

}  // namespace
