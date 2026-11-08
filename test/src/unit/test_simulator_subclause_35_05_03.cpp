#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiContextChain, ContextEntrySetsScopeFromDeclScope) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "top.dut";
  rt.EnterContextImportCall("my_ctx_import", sc);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");
}

TEST(DpiContextChain, LeaveImportCallRestoresScope) {
  DpiRuntime rt;
  DpiScope outer;
  outer.name = "outer";
  rt.PushScope(outer);

  DpiScope inner;
  inner.name = "top.dut";
  rt.EnterContextImportCall("ctx_import", inner);
  rt.LeaveImportCall();

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "outer");
}

TEST(DpiContextChain, NoncontextImportRejectsExportCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(7);
  };
  rt.RegisterExport(exp);
  rt.EnterNoncontextImportCall("nonctx_import");

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiContextChain, ContextImportPermitsExportCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(42);
  };
  rt.RegisterExport(exp);
  DpiScope sc;
  sc.name = "top.dut";
  rt.EnterContextImportCall("ctx_import", sc);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 42);
}

TEST(DpiContextChain, ContextNotPromotedToNoncontextNestedCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);
  DpiScope sc;
  sc.name = "scope_root";
  rt.EnterContextImportCall("ctx_root", sc);
  rt.EnterNoncontextImportCall("nonctx_inner");

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiContextChain, ImportCallDepthTracksNesting) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "s";
  EXPECT_EQ(rt.ImportCallDepth(), 0u);
  rt.EnterContextImportCall("a", sc);
  EXPECT_EQ(rt.ImportCallDepth(), 1u);
  rt.EnterNoncontextImportCall("b");
  EXPECT_EQ(rt.ImportCallDepth(), 2u);
  rt.LeaveImportCall();
  EXPECT_EQ(rt.ImportCallDepth(), 1u);
  rt.LeaveImportCall();
  EXPECT_EQ(rt.ImportCallDepth(), 0u);
}

TEST(DpiContextChain, ChainRootIsContextReflectsRoot) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "root";
  rt.EnterContextImportCall("root_call", sc);
  rt.EnterNoncontextImportCall("inner_call");
  EXPECT_TRUE(rt.ChainRootIsContext());
}

TEST(DpiContextChain, SvSetScopeUpdatesChainContext) {
  DpiRuntime rt;
  DpiScope decl_scope;
  decl_scope.name = "decl";
  rt.EnterContextImportCall("ctx_import", decl_scope);

  DpiScope alt;
  alt.name = "alt";
  rt.SetScope(&alt);

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "alt");
}

TEST(DpiContextChain, ExportReturnRestoresChainContext) {
  DpiRuntime rt;
  DpiScope ctx_scope;
  ctx_scope.name = "ctx_scope";
  DpiScope altered;
  altered.name = "altered_during_export";

  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [&rt, &altered](const std::vector<DpiArgValue>&) -> DpiArgValue {
    rt.SetScope(&altered);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(exp);
  rt.EnterContextImportCall("ctx", ctx_scope);

  DpiArgValue result;
  rt.CallExportFromImport("sv_export", {}, &result);

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "ctx_scope");
}

TEST(DpiContextChain, SameImportInBothContextAndNoncontextChains) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "scope";

  rt.EnterContextImportCall("shared_import", sc);
  EXPECT_TRUE(rt.ChainRootIsContext());
  rt.LeaveImportCall();

  rt.EnterNoncontextImportCall("shared_import");
  EXPECT_FALSE(rt.ChainRootIsContext());
  rt.LeaveImportCall();
}

TEST(DpiContextChain, CallExportFromImportWithEmptyChainIsRejected) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(99);
  };
  rt.RegisterExport(exp);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiContextChain, LeaveImportCallWithEmptyChainIsSafe) {
  DpiRuntime rt;
  rt.LeaveImportCall();
  EXPECT_EQ(rt.ImportCallDepth(), 0u);
}

TEST(DpiContextChain, ContextScopePreservesHierarchicalName) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "top.dut.sub.leaf";
  rt.EnterContextImportCall("ctx_import", sc);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut.sub.leaf");
}

TEST(DpiContextChain, ExportCalledFromForeignScopeIsRejected) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.scope_name = "top.scope_a";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(1);
  };
  rt.RegisterExport(exp);
  DpiScope ctx_scope;
  ctx_scope.name = "top.scope_b";
  rt.EnterContextImportCall("ctx", ctx_scope);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kScopeMismatch);
}

TEST(DpiContextChain, ExportCalledFromMatchingScopeIsPermitted) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.scope_name = "top.shared";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(7);
  };
  rt.RegisterExport(exp);
  DpiScope ctx_scope;
  ctx_scope.name = "top.shared";
  rt.EnterContextImportCall("ctx", ctx_scope);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 7);
}

TEST(DpiContextChain, SvSetScopeEnablesForeignScopeExportCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.scope_name = "top.scope_a";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(3);
  };
  rt.RegisterExport(exp);
  DpiScope ctx_scope;
  ctx_scope.name = "top.scope_b";
  rt.EnterContextImportCall("ctx", ctx_scope);

  DpiScope retargeted;
  retargeted.name = "top.scope_a";
  rt.SetScope(&retargeted);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
}

TEST(DpiContextChain, ContextImportCallIsOptimizationBarrier) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.sv_name = "ctx_import";
  func.is_context = true;
  rt.RegisterImport(func);
  EXPECT_TRUE(rt.IsImportCallOptimizationBarrier("ctx_import"));
}

TEST(DpiContextChain, NoncontextImportCallIsNotOptimizationBarrier) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.sv_name = "plain_import";
  func.is_context = false;
  rt.RegisterImport(func);
  EXPECT_FALSE(rt.IsImportCallOptimizationBarrier("plain_import"));
}

struct TwoScopesExportingOneName {
  DpiRuntime rt;

  TwoScopesExportingOneName() {
    Register("top.a", 1);
    Register("top.b", 2);
  }

  void Register(const char* scope_name, int answer) {
    DpiRtExport exp;
    exp.sv_name = "sv_export";
    exp.scope_name = scope_name;
    exp.impl = [answer](const std::vector<DpiArgValue>&) -> DpiArgValue {
      return DpiArgValue::FromInt(answer);
    };
    rt.RegisterExport(exp);
  }

  int CallingFrom(const char* scope_name) {
    DpiScope decl_scope;
    decl_scope.name = scope_name;
    rt.EnterContextImportCall("ctx", decl_scope);
    DpiArgValue result = DpiArgValue::FromInt(-1);
    rt.CallExportFromImport("sv_export", {}, &result);
    rt.LeaveImportCall();
    return result.AsInt();
  }
};

TEST(DpiExportInstances, BothScopesInstancesAreRegistered) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.rt.ExportCount(), 2u);
}

TEST(DpiExportInstances, AnInstanceIsFoundUnderTheScopeThatDeclaredIt) {
  TwoScopesExportingOneName both;
  const auto* found = both.rt.FindExportInScope("sv_export", "top.a");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->scope_name, "top.a");
}

TEST(DpiExportInstances, NoInstanceIsFoundUnderAScopeThatDeclaredNone) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.rt.FindExportInScope("sv_export", "top.c"), nullptr);
}

TEST(DpiExportInstances, TheInstanceThatRunsIsTheOneTheChainsScopeDeclares) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.CallingFrom("top.a"), 1);
}

TEST(DpiExportInstances, TheOtherScopeRunsItsOwnInstance) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.CallingFrom("top.b"), 2);
}

TEST(DpiExportInstances, SvSetScopeSelectsTheInstanceInTheNamedScope) {
  TwoScopesExportingOneName both;
  DpiScope decl_scope;
  decl_scope.name = "top.a";
  both.rt.EnterContextImportCall("ctx", decl_scope);

  DpiScope named;
  named.name = "top.b";
  both.rt.SetScope(&named);

  DpiArgValue result = DpiArgValue::FromInt(-1);
  both.rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(result.AsInt(), 2);
}

TEST(DpiExportInstances, AnExportUnderNoScopeIsReachedFromAnyScope) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(8);
  };
  rt.RegisterExport(exp);

  DpiScope decl_scope;
  decl_scope.name = "top.anywhere";
  rt.EnterContextImportCall("ctx", decl_scope);

  DpiArgValue result = DpiArgValue::FromInt(-1);
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 8);
}

TEST(DpiContextChain, ANoncontextCallsScopeChangeDoesNotOutliveIt) {
  DpiRuntime rt;
  DpiScope caller;
  caller.name = "top.caller";
  rt.PushScope(caller);

  rt.EnterNoncontextImportCall("plain_import");
  DpiScope elsewhere;
  elsewhere.name = "top.elsewhere";
  rt.SetScope(&elsewhere);
  rt.LeaveImportCall();

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.caller");
}

TEST(DpiContextChain, ANoncontextCallSettingNoScopeLeavesTheCallersScope) {
  DpiRuntime rt;
  DpiScope caller;
  caller.name = "top.caller";
  rt.PushScope(caller);

  rt.EnterNoncontextImportCall("plain_import");
  rt.LeaveImportCall();

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.caller");
}

TEST(DpiContextChain, ANoncontextCallLeavesTheCallersScopeAfterANestedScope) {
  DpiRuntime rt;
  DpiScope caller;
  caller.name = "top.caller";
  rt.PushScope(caller);

  rt.EnterNoncontextImportCall("plain_import");
  DpiScope nested;
  nested.name = "top.nested";
  rt.EnterContextImportCall("ctx_inner", nested);
  rt.LeaveImportCall();
  rt.LeaveImportCall();

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.caller");
}

TEST(DpiContextChain, SvSetScopeDoesNotMakeANoncontextCallContext) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.scope_name = "top.dut";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(5);
  };
  rt.RegisterExport(exp);

  rt.EnterNoncontextImportCall("plain_import");
  DpiScope named;
  named.name = "top.dut";
  rt.SetScope(&named);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_export", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
}

struct ForeignRuntimeInstall {
  explicit ForeignRuntimeInstall(DpiRuntime* rt) { DpiSetForeignRuntime(rt); }
  ~ForeignRuntimeInstall() { DpiSetForeignRuntime(nullptr); }
};

TEST(DpiForeignScope, SvSetScopeMovesTheScopeTheRegistryReports) {
  DpiRuntime rt;
  ForeignRuntimeInstall installed(&rt);
  DpiScope decl;
  decl.name = "top.dut";
  rt.EnterContextImportCall("ctx_import", decl);

  const DpiScope* alt = DpiRegisterScope("top.other");
  svSetScope(const_cast<DpiScope*>(alt));

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.other");
}

TEST(DpiForeignScope, SvGetScopeReportsTheScopeTheRegistryHolds) {
  DpiRuntime rt;
  ForeignRuntimeInstall installed(&rt);
  DpiScope decl;
  decl.name = "top.dut";
  rt.EnterContextImportCall("ctx_import", decl);

  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(svGetScope(), static_cast<const void*>(rt.CurrentScope()));
}

TEST(DpiForeignScope, WithNoRegistryInstalledTheScopeIsTheCLayersOwn) {
  DpiSetForeignRuntime(nullptr);
  const DpiScope* standalone = DpiRegisterScope("standalone");
  svSetScope(const_cast<DpiScope*>(standalone));
  EXPECT_EQ(svGetScope(), static_cast<const void*>(standalone));
}

}  // namespace
