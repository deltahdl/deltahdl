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

// ---------------------------------------------------------------------------
// One exported subroutine, one instance per instantiated scope.
// ---------------------------------------------------------------------------
//
// §35.5.3 says which export a call from an import reaches:
//
//   When an import invokes the svSetScope utility prior to calling the export,
//   it sets the context explicitly. Otherwise, the context will be the context
//   of the instantiated scope where the import declaration is located. Because
//   imports with diverse instantiated scopes can export the same subroutine,
//   multiple instances of such an export can exist after elaboration. Prior to
//   any invocations of svSetScope, these export instances would have different
//   contexts, which would reflect their imported caller's instantiated scope.
//
// A name is therefore not enough to say which export a call runs. Two scopes
// can each export a subroutine of one name, and the call an import makes runs
// the instance belonging to the chain's current scope: the import declaration's
// instantiated scope, or whatever scope svSetScope has named since.
//
// DpiRuntime::FindExportInScope answers by scope and name together, and
// DpiRuntime::CallExportFromImport asks it before it asks by name. Falling back
// to the name is what reaches an export registered under no scope at all, which
// is how most of this file registers one.

// Two instantiated scopes exporting one name, each instance answering with its
// own value so that a case can say which of them ran.
struct TwoScopesExportingOneName {
  DpiRuntime rt;

  TwoScopesExportingOneName() {
    // Registered in this order so that the name index holds top.b: a lookup by
    // name alone reaches top.b's instance whichever scope is calling.
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

  // Opens a context import chain whose declaration sits in `scope_name`, calls
  // the export from it and yields what the instance that ran answered. A call
  // the runtime refuses yields -1, which no instance answers.
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

// §35.5.3: both instances exist once elaboration is done, so registering the
// second does not displace the first.
TEST(DpiExportInstances, BothScopesInstancesAreRegistered) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.rt.ExportCount(), 2u);
}

// The instance a scope declares is reachable under that scope.
TEST(DpiExportInstances, AnInstanceIsFoundUnderTheScopeThatDeclaredIt) {
  TwoScopesExportingOneName both;
  const auto* found = both.rt.FindExportInScope("sv_export", "top.a");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->scope_name, "top.a");
}

// And a scope that declared no export of the name has no instance of it. This
// is what makes the lookup say something: a lookup answering for every scope
// would satisfy the case above without telling the instances apart.
TEST(DpiExportInstances, NoInstanceIsFoundUnderAScopeThatDeclaredNone) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.rt.FindExportInScope("sv_export", "top.c"), nullptr);
}

// §35.5.3: the export instance that runs reflects the imported caller's
// instantiated scope. A chain rooted in top.a runs top.a's instance, though the
// name was registered afterwards from top.b.
TEST(DpiExportInstances, TheInstanceThatRunsIsTheOneTheChainsScopeDeclares) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.CallingFrom("top.a"), 1);
}

// The other scope runs its own instance, so the choice follows the caller
// rather than always landing on one instance.
TEST(DpiExportInstances, TheOtherScopeRunsItsOwnInstance) {
  TwoScopesExportingOneName both;
  EXPECT_EQ(both.CallingFrom("top.b"), 2);
}

// §35.5.3: an import that invokes svSetScope before calling the export sets the
// context explicitly, so the instance that runs is the one the named scope
// declares rather than the one the declaration's scope declares.
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

// An export registered under no scope names no instance, and is reached from a
// chain in any scope.
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

// ---------------------------------------------------------------------------
// What a noncontext import call leaves behind, and what it cannot become.
// ---------------------------------------------------------------------------
//
// §35.5.3: "An imported subroutine not specified as context shall not access
// any data objects from SystemVerilog other than its actual arguments. Only the
// actual arguments can be affected (read or written) by its call." A scope such
// a call sets is therefore not something whatever runs after it can read: the
// call ends with the scope its caller had.

// A scope a noncontext import sets does not outlive the call that set it.
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

// And a noncontext call that sets no scope leaves the one it found. The restore
// returns the caller's scope rather than discarding it, which a runtime
// clearing the scope on every leave would fail.
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

// The caller's scope is still the caller's after a noncontext call that opened
// and closed a scope of its own while it ran. Restoring reads the scope stack
// afresh for exactly this reason: opening a scope can move the stack's
// elements, so the address the caller's scope had when the call began is not
// the address it has when the call returns.
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

// §35.5.3: "The context characteristic of a DPI import call cannot be
// dynamically changed after the initial call to the import subroutine in the
// DPI supported language." Naming the export's own scope is what would let a
// context call reach it, and it does not make this call a context one.
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

}  // namespace
