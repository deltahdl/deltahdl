#include <gtest/gtest.h>

#include <array>
#include <string_view>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §H.9.2: DPI imported and exported tasks and functions can be declared in a
// module, program, interface, package, compilation-unit scope or generate
// declarative scope -- six scopes, in that order.
TEST(DpiSubroutineContext, ASubroutineCanBeDeclaredInSixDeclarativeScopes) {
  const std::array<DpiDeclarativeScope, 6> kScopes = DpiDeclarativeScopes();
  EXPECT_EQ(kScopes[0], DpiDeclarativeScope::kModule);
  EXPECT_EQ(kScopes[1], DpiDeclarativeScope::kProgram);
  EXPECT_EQ(kScopes[2], DpiDeclarativeScope::kInterface);
  EXPECT_EQ(kScopes[3], DpiDeclarativeScope::kPackage);
  EXPECT_EQ(kScopes[4], DpiDeclarativeScope::kCompilationUnit);
  EXPECT_EQ(kScopes[5], DpiDeclarativeScope::kGenerate);
}

// §H.9.2: the context of an imported or exported subroutine corresponds to
// the fully qualified name of the subroutine minus the subroutine name
// itself.
TEST(DpiSubroutineContext, TheContextIsTheQualifiedNameMinusTheSubroutines) {
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.f"), "top.i1_m");
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.genblk1.f"),
            "top.i1_m.genblk1");
  EXPECT_EQ(DpiContextOfQualifiedName("pkg::f"), "pkg");
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.pkg::f"), "top.i1_m.pkg");
  EXPECT_EQ(DpiContextOfQualifiedName("f"), "");
}

// §H.9.2: a context import executes in the context of the instantiated scope
// surrounding its declaration, seeing that scope's other variables without
// qualification, which is not the context of its call site, anywhere in the
// design hierarchy.
TEST(DpiSubroutineContext, AContextImportSeesItsOwnScopesVariablesUnqualified) {
  const std::string_view kContext = DpiContextOfQualifiedName("top.i1_m.f");
  EXPECT_TRUE(DpiHasUnqualifiedVisibility(kContext, "top.i1_m"));
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.elsewhere"));
  EXPECT_EQ(DpiContextOfSubroutine(kContext, "top.elsewhere"), "top.i1_m");
}

// §H.9.2: the context property is transitive through the imported and
// exported context subroutines declared in one scope: an export available in
// the context an import runs in is callable without any use of svSetScope,
// and one in another context is not.
TEST(DpiSubroutineContext, AnExportInTheSameContextNeedsNoSvSetScope) {
  EXPECT_TRUE(DpiExportIsCallableWithoutSvSetScope(
      DpiContextOfQualifiedName("top.i1_m.f"),
      DpiContextOfQualifiedName("top.i1_m.g")));
  EXPECT_FALSE(DpiExportIsCallableWithoutSvSetScope(
      DpiContextOfQualifiedName("top.i1_m.f"),
      DpiContextOfQualifiedName("top.i2_m.g")));
}

// §H.9.2: when control passes across the boundary between SystemVerilog and a
// DPI import call chain with the context property, the import's context is
// potentially set or reset; a chain without the property has no context to
// change.
TEST(DpiSubroutineContext, TheImportsContextMayChangeAcrossTheBoundary) {
  EXPECT_TRUE(DpiImportContextMayChangeAcrossBoundary(true));
  EXPECT_FALSE(DpiImportContextMayChangeAcrossBoundary(false));
}

// §H.9.2: user code behavior is defined across a call of an export and its
// return, and undefined for C code that circumvents SystemVerilog exports
// unwinding across the boundary by setjmp and longjmp.
TEST(DpiSubroutineContext, UnwindingAcrossTheBoundaryIsUndefined) {
  EXPECT_TRUE(
      DpiBehaviorIsDefinedAcross(DpiBoundaryCrossing::kExportCallAndReturn));
  EXPECT_FALSE(DpiBehaviorIsDefinedAcross(
      DpiBoundaryCrossing::kUnwindingBySetjmpAndLongjmp));
}

// §H.9.2's example under the runtime: a native function g() exported from
// top.i1_m, called by a native f() and by f'(), an equivalent context import
// declared in the same scope. The system behaves identically whichever is in
// the chain above g(), and g() has its proper execution context in both.
struct ExportedGInScope {
  DpiRuntime rt;

  ExportedGInScope() {
    DpiRtExport g;
    g.sv_name = "g";
    g.scope_name = "top.i1_m";
    g.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
      return DpiArgValue::FromInt(7);
    };
    rt.RegisterExport(g);
  }
};

// Native f() calling g(): the call reaches g() and yields its result.
TEST(DpiSubroutineContext, ANativeFunctionCallingTheExportReachesIt) {
  ExportedGInScope design;
  EXPECT_EQ(design.rt.CallExport("g", {}).AsInt(), 7);
}

// The context import f'() declared in top.i1_m calling g(): the same result,
// with no svSetScope, because g() is available in the context f'() runs in.
TEST(DpiSubroutineContext, AContextImportInTheSameScopeCallsTheExportAlike) {
  ExportedGInScope design;
  DpiScope decl_scope;
  decl_scope.name = "top.i1_m";
  design.rt.EnterContextImportCall("f_prime", decl_scope);
  DpiArgValue result = DpiArgValue::FromInt(-1);
  EXPECT_EQ(design.rt.CallExportFromImport("g", {}, &result),
            DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), design.rt.CallExport("g", {}).AsInt());
  design.rt.LeaveImportCall();
}

// An import declared in another scope is not in g()'s context: without an
// svSetScope naming top.i1_m the runtime refuses the call, which is what makes
// the transitivity above a statement about the scope and not about the name.
TEST(DpiSubroutineContext, AContextImportInAnotherScopeNeedsSvSetScope) {
  ExportedGInScope design;
  DpiScope decl_scope;
  decl_scope.name = "top.i2_m";
  design.rt.EnterContextImportCall("f_prime", decl_scope);
  DpiArgValue result = DpiArgValue::FromInt(-1);
  EXPECT_EQ(design.rt.CallExportFromImport("g", {}, &result),
            DpiExportCallStatus::kScopeMismatch);
  DpiScope named;
  named.name = "top.i1_m";
  design.rt.SetScope(&named);
  EXPECT_EQ(design.rt.CallExportFromImport("g", {}, &result),
            DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 7);
  design.rt.LeaveImportCall();
}

// §H.9.2 with §35.5.3: across the boundary the import's context is set or
// reset by the simulator: an export that leaves another scope set returns to
// its caller with the context the caller had when it invoked the export.
TEST(DpiSubroutineContext, TheContextIsResetWhenTheExportReturns) {
  DpiRuntime rt;
  DpiScope elsewhere;
  elsewhere.name = "top.elsewhere";
  DpiRtExport g;
  g.sv_name = "g";
  g.scope_name = "top.i1_m";
  g.impl = [&rt, &elsewhere](const std::vector<DpiArgValue>&) -> DpiArgValue {
    rt.SetScope(&elsewhere);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(g);

  DpiScope decl_scope;
  decl_scope.name = "top.i1_m";
  rt.EnterContextImportCall("f_prime", decl_scope);
  const DpiScope* before = rt.GetScope();
  ASSERT_NE(before, nullptr);
  EXPECT_EQ(rt.CallExportFromImport("g", {}, nullptr),
            DpiExportCallStatus::kOk);
  EXPECT_EQ(rt.GetScope(), before);
  EXPECT_EQ(rt.GetScope()->name, "top.i1_m");
  rt.LeaveImportCall();
}

}  // namespace
