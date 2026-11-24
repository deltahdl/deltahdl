#include <gtest/gtest.h>

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "helpers_dpi_scope_names.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

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

TEST(DpiAndVpiContext,
     DpiContextIsTheDeclarationSitesAndVpiContextTheCallSites) {
  EXPECT_EQ(DpiContextSiteOf(DpiContextNotion::kDpiContext),
            DpiContextSite::kDeclarationSite);
  EXPECT_EQ(DpiContextSiteOf(DpiContextNotion::kVpiContext),
            DpiContextSite::kCallSite);
}

TEST(DpiAndVpiContext, ASubroutineExecutesInItsDeclarationsInstantiatedScope) {
  EXPECT_EQ(DpiContextOfSubroutine("top.i1_m", "top.distant.region"),
            "top.i1_m");
  EXPECT_NE(DpiContextOfSubroutine("top.i1_m", "top.distant.region"),
            "top.distant.region");
}

TEST(DpiAndVpiContext, UnqualifiedVisibilityIsOfTheInstancesOwnVariablesOnly) {
  const std::string_view kContext =
      DpiContextOfSubroutine("top.i1_m", "top.distant.region");
  EXPECT_TRUE(DpiHasUnqualifiedVisibility(kContext, "top.i1_m"));
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.distant.region"));
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.i2_m"));
}

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

TEST(DpiAndVpiContext, OneExportHasOneInstancePerImportingInstantiatedScope) {
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m", "top.i2_m"}), 2u);
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m", "top.i2_m", "top.i1_m"}), 2u);
  EXPECT_EQ(DpiExportInstanceCount({"top.i1_m"}), 1u);
  EXPECT_EQ(DpiExportInstanceCount({}), 0u);
}

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

TEST(DpiAndVpiContext, TheRuntimeHasOneExportInstancePerInstantiatedScope) {
  ModuleInstantiatedTwice m;
  EXPECT_EQ(m.rt.ExportCount(),
            DpiExportInstanceCount({"top.i1_m", "top.i2_m"}));
  EXPECT_EQ(m.InstanceReachedFrom("top.i2_m", std::nullopt), 2);
  EXPECT_EQ(m.InstanceReachedFrom("top.i1_m", std::nullopt), 1);
}

TEST(DpiAndVpiContext, TheRuntimeRunsTheInstanceSvSetScopeNamedBeforeTheCall) {
  ModuleInstantiatedTwice m;
  EXPECT_EQ(m.InstanceReachedFrom("top.i2_m", "top.i1_m"), 1);
}

TEST(ContextOfADesignsImport,
     DISABLED_AHierarchicalCallRunsInTheDeclaringInstance) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module m;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "endmodule\n"
      "module caller;\n"
      "  int r;\n"
      "  initial #1 r = site.i1_m.see_scope();\n"
      "endmodule\n"
      "module site;\n"
      "  m i1_m();\n"
      "  caller i2();\n"
      "endmodule\n",
      "annex_h_09_01_hierarchical_call");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"site.i1_m", "site.i1_m"}));
}

TEST(ContextOfADesignsImport,
     DISABLED_AHierarchicalTaskCallRunsInTheDeclaringInstance) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module m;\n"
      "  import \"DPI-C\" context task see_scope();\n"
      "  initial see_scope();\n"
      "endmodule\n"
      "module caller;\n"
      "  initial #1 tsite.i1_m.see_scope();\n"
      "endmodule\n"
      "module tsite;\n"
      "  m i1_m();\n"
      "  caller i2();\n"
      "endmodule\n",
      "annex_h_09_01_hierarchical_task");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"tsite.i1_m", "tsite.i1_m"}));
}

TEST(ContextOfADesignsImport, ANativeCallerInTheSameInstanceKeepsItsContext) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module m;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  function int through(); return see_scope(); endfunction\n"
      "endmodule\n"
      "module caller;\n"
      "  int r;\n"
      "  initial r = nsite.i1_m.through();\n"
      "endmodule\n"
      "module nsite;\n"
      "  m i1_m();\n"
      "  caller i2();\n"
      "endmodule\n",
      "annex_h_09_01_native_caller");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"nsite.i1_m"}));
}

}  // namespace
