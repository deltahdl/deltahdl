#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.5.3: when SystemVerilog calls a context import, the chain context is
// set to the import declaration's instantiated scope.
TEST(DpiContextChain, ContextEntrySetsScopeFromDeclScope) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "top.dut";
  rt.EnterContextImportCall("my_ctx_import", sc);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");
}

// §35.5.3: leaving the context import call returns scope to its prior value.
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

// §35.5.3: a noncontext import call cannot legally call an export.
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

// §35.5.3: a context import call can call an export and receive its result.
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

// §35.5.3: the context property is not transitively promoted to inner calls.
// A noncontext import nested inside a context import call cannot itself call
// an export — the innermost frame's property governs the call.
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

// §35.5.3: call-chain depth reflects nested import calls.
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

// §35.5.3: ChainRootIsContext reports the root frame's property regardless
// of inner frames.
TEST(DpiContextChain, ChainRootIsContextReflectsRoot) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "root";
  rt.EnterContextImportCall("root_call", sc);
  rt.EnterNoncontextImportCall("inner_call");
  EXPECT_TRUE(rt.ChainRootIsContext());
}

// §35.5.3: an svSetScope call from inside an import chain replaces the
// chain's current context with the indicated scope.
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

// §35.5.3: when an export call made from a context import chain returns,
// the chain context is restored to the value it had at the point of the
// call, even if the export's body mutated the scope.
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

// §35.5.3: the context characteristic attaches to the calling chain, not to
// a particular imported subroutine — the same import can root one chain as
// context and another as noncontext.
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

// §35.5.3 edge case: an export call has no business running outside an
// import chain. With no active import call, the runtime should treat the
// attempt the same as a noncontext chain rather than performing the call.
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

// Robustness: a Leave on an empty chain should be a no-op, not a crash.
// This protects against unbalanced enter/leave bookkeeping in callers.
TEST(DpiContextChain, LeaveImportCallWithEmptyChainIsSafe) {
  DpiRuntime rt;
  rt.LeaveImportCall();
  EXPECT_EQ(rt.ImportCallDepth(), 0u);
}

// §35.5.3: the scope supplied to a context import is the fully qualified
// instance name of the import declaration; the runtime preserves whatever
// hierarchical name the caller provides without truncating dots.
TEST(DpiContextChain, ContextScopePreservesHierarchicalName) {
  DpiRuntime rt;
  DpiScope sc;
  sc.name = "top.dut.sub.leaf";
  rt.EnterContextImportCall("ctx_import", sc);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut.sub.leaf");
}

// §35.5.3: an export call from a context chain is permitted only when the
// export's declaration scope matches the chain's current scope; calling
// across scopes without first using svSetScope is an error.
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

// §35.5.3: a context import can call an export defined in the same scope
// directly.
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

// §35.5.3: svSetScope updates the chain context, after which an export
// defined in the newly indicated scope becomes directly callable.
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

// §35.5.3: a call to a context-declared import acts as a barrier for the
// SystemVerilog compiler's optimizations; the runtime reports this so the
// compiler can avoid folding or eliminating the call.
TEST(DpiContextChain, ContextImportCallIsOptimizationBarrier) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.sv_name = "ctx_import";
  func.is_context = true;
  rt.RegisterImport(func);
  EXPECT_TRUE(rt.IsImportCallOptimizationBarrier("ctx_import"));
}

// §35.5.3: a noncontext import call is not a barrier — its effects are
// limited to its actual arguments, so the compiler is free to optimize.
TEST(DpiContextChain, NoncontextImportCallIsNotOptimizationBarrier) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.sv_name = "plain_import";
  func.is_context = false;
  rt.RegisterImport(func);
  EXPECT_FALSE(rt.IsImportCallOptimizationBarrier("plain_import"));
}

}  // namespace
