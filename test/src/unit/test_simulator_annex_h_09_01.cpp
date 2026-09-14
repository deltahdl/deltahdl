#include <gtest/gtest.h>

#include <optional>
#include <string_view>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §H.9.1: the term context means different things for the two categories of
// subroutine. A DPI import is a proxy for a native SystemVerilog task or
// function and has the notion a native one has, DPI context; a VPI function
// has VPI context.
TEST(DpiAndVpiContext, AnImportHasTheDpiContextOfTheNativeSubroutineItProxies) {
  EXPECT_EQ(DpiContextNotionOf(DpiContextUser::kDpiImportedSubroutine),
            DpiContextNotion::kDpiContext);
  EXPECT_EQ(DpiContextNotionOf(DpiContextUser::kDpiImportedSubroutine),
            DpiContextNotionOf(DpiContextUser::kNativeSystemVerilogSubroutine));
}

TEST(DpiAndVpiContext, AVpiFunctionHasVpiContext) {
  EXPECT_EQ(DpiContextNotionOf(DpiContextUser::kVpiFunction),
            DpiContextNotion::kVpiContext);
  EXPECT_NE(DpiContextNotionOf(DpiContextUser::kVpiFunction),
            DpiContextNotionOf(DpiContextUser::kDpiImportedSubroutine));
}

// §H.9.1: DPI context is the declaration site's -- a native subroutine always
// operates in the scope of its declaration, and an import executes in the
// context of its surrounding declarative scope rather than that of its call
// sites -- while VPI context is associated with the call site, where the VPI
// programming model retrieves its context handle.
TEST(DpiAndVpiContext,
     DpiContextIsTheDeclarationSitesAndVpiContextTheCallSites) {
  EXPECT_EQ(DpiContextSiteOf(DpiContextNotion::kDpiContext),
            DpiContextSite::kDeclarationSite);
  EXPECT_EQ(DpiContextSiteOf(DpiContextNotion::kVpiContext),
            DpiContextSite::kCallSite);
}

// §H.9.1's example: f() declared in module m instantiated as top.i1_m is
// called through a hierarchical reference from a distant design region, and
// executes in the instantiated scope top.i1_m, not the caller's.
TEST(DpiAndVpiContext, ASubroutineExecutesInItsDeclarationsInstantiatedScope) {
  EXPECT_EQ(DpiContextOfSubroutine("top.i1_m", "top.distant.region"),
            "top.i1_m");
  EXPECT_NE(DpiContextOfSubroutine("top.i1_m", "top.distant.region"),
            "top.distant.region");
}

// §H.9.1: in that context f() has unqualified visibility only for the
// variables local to that specific instance of m, and none for variables in
// the calling code's scope.
TEST(DpiAndVpiContext, UnqualifiedVisibilityIsOfTheInstancesOwnVariablesOnly) {
  const std::string_view kContext =
      DpiContextOfSubroutine("top.i1_m", "top.distant.region");
  EXPECT_TRUE(DpiHasUnqualifiedVisibility(kContext, "top.i1_m"));
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.distant.region"));
  // Another instance of the same module m is another scope: its variables are
  // not the instance's own.
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.i2_m"));
}

// §H.9.1: an import that invokes svSetScope before calling an export sets the
// export's context explicitly; otherwise the context is the instantiated scope
// where the import declaration is located.
TEST(DpiAndVpiContext,
     AnExportsContextIsSetBySvSetScopeOrElseIsTheImportsScope) {
  EXPECT_EQ(DpiExportContextOriginOf(true),
            DpiExportContextOrigin::kSetExplicitlyBySvSetScope);
  EXPECT_EQ(DpiExportContextOriginOf(false),
            DpiExportContextOrigin::kImportDeclarationsInstantiatedScope);
  EXPECT_EQ(DpiContextOfExportCalledFromImport("top.i1_m", "top.i2_m"),
            "top.i2_m");
  EXPECT_EQ(DpiContextOfExportCalledFromImport("top.i1_m", std::nullopt),
            "top.i1_m");
}

// §H.9.1: imports with diverse instantiated scopes can export the same
// subroutine, so multiple instances of the export exist after elaboration --
// one per instantiated scope, two imports in one scope sharing an instance.
TEST(DpiAndVpiContext, OneExportHasOneInstancePerImportingInstantiatedScope) {
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m", "top.i2_m"}), 2u);
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m", "top.i2_m", "top.i1_m"}), 2u);
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m"}), 1u);
  EXPECT_EQ(DpiExportInstanceCount({}), 0u);
}

// The runtime under §H.9.1's example: module m, instantiated as top.i1_m and
// top.i2_m, exports one subroutine, so two instances of it exist, each
// answering with its own instance number.
struct ModuleInstantiatedTwice {
  DpiRuntime rt;

  ModuleInstantiatedTwice() {
    Register("top.i1_m", 1);
    Register("top.i2_m", 2);
  }

  void Register(const char* scope_name, int instance) {
    DpiRtExport exp;
    exp.sv_name = "sv_export";
    exp.scope_name = scope_name;
    exp.impl = [instance](const std::vector<DpiArgValue>&) -> DpiArgValue {
      return DpiArgValue::FromInt(instance);
    };
    rt.RegisterExport(exp);
  }

  // Calls the export from a context import declared in `import_scope`, after
  // an svSetScope naming `set_scope` where one is given, and yields the
  // instance that ran.
  int InstanceReachedFrom(const char* import_scope,
                          std::optional<const char*> set_scope) {
    DpiScope decl_scope;
    decl_scope.name = import_scope;
    rt.EnterContextImportCall("ctx", decl_scope);
    DpiScope named;
    if (set_scope.has_value()) {
      named.name = *set_scope;
      rt.SetScope(&named);
    }
    DpiArgValue result = DpiArgValue::FromInt(-1);
    rt.CallExportFromImport("sv_export", {}, &result);
    rt.LeaveImportCall();
    return result.AsInt();
  }
};

// §H.9.1: prior to any invocation of svSetScope, the export instances have
// different contexts reflecting their imported caller's instantiated scope: an
// import declared in top.i2_m reaches top.i2_m's instance and one declared in
// top.i1_m reaches top.i1_m's.
TEST(DpiAndVpiContext, TheRuntimeHasOneExportInstancePerInstantiatedScope) {
  ModuleInstantiatedTwice m;
  EXPECT_EQ(m.rt.ExportCount(),
            DpiExportInstanceCount({"top.i1_m", "top.i2_m"}));
  EXPECT_EQ(m.InstanceReachedFrom("top.i2_m", std::nullopt), 2);
  EXPECT_EQ(m.InstanceReachedFrom("top.i1_m", std::nullopt), 1);
}

// §H.9.1: an svSetScope before the call sets the context explicitly, so the
// import declared in top.i2_m reaches top.i1_m's instance when it names that
// scope.
TEST(DpiAndVpiContext, TheRuntimeRunsTheInstanceSvSetScopeNamedBeforeTheCall) {
  ModuleInstantiatedTwice m;
  EXPECT_EQ(m.InstanceReachedFrom("top.i2_m", "top.i1_m"), 1);
}

}  // namespace
