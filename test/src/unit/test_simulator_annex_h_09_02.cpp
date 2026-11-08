#include <gtest/gtest.h>

#include <array>
#include <string_view>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiSubroutineContext, ASubroutineCanBeDeclaredInSixDeclarativeScopes) {
  const std::array<DpiDeclarativeScope, 6> kScopes = DpiDeclarativeScopes();
  EXPECT_EQ(kScopes[0], DpiDeclarativeScope::kModule);
  EXPECT_EQ(kScopes[1], DpiDeclarativeScope::kProgram);
  EXPECT_EQ(kScopes[2], DpiDeclarativeScope::kInterface);
  EXPECT_EQ(kScopes[3], DpiDeclarativeScope::kPackage);
  EXPECT_EQ(kScopes[4], DpiDeclarativeScope::kCompilationUnit);
  EXPECT_EQ(kScopes[5], DpiDeclarativeScope::kGenerate);
}

TEST(DpiSubroutineContext, TheContextIsTheQualifiedNameMinusTheSubroutines) {
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.f"), "top.i1_m");
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.genblk1.f"),
            "top.i1_m.genblk1");
  EXPECT_EQ(DpiContextOfQualifiedName("pkg::f"), "pkg");
  EXPECT_EQ(DpiContextOfQualifiedName("top.i1_m.pkg::f"), "top.i1_m.pkg");
  EXPECT_EQ(DpiContextOfQualifiedName("f"), "");
}

TEST(DpiSubroutineContext, AContextImportSeesItsOwnScopesVariablesUnqualified) {
  const std::string_view kContext = DpiContextOfQualifiedName("top.i1_m.f");
  EXPECT_TRUE(DpiHasUnqualifiedVisibility(kContext, "top.i1_m"));
  EXPECT_FALSE(DpiHasUnqualifiedVisibility(kContext, "top.elsewhere"));
  EXPECT_EQ(DpiContextOfSubroutine(kContext, "top.elsewhere"), "top.i1_m");
}

TEST(DpiSubroutineContext, AnExportInTheSameContextNeedsNoSvSetScope) {
  EXPECT_TRUE(DpiExportIsCallableWithoutSvSetScope(
      DpiContextOfQualifiedName("top.i1_m.f"),
      DpiContextOfQualifiedName("top.i1_m.g")));
  EXPECT_FALSE(DpiExportIsCallableWithoutSvSetScope(
      DpiContextOfQualifiedName("top.i1_m.f"),
      DpiContextOfQualifiedName("top.i2_m.g")));
}

TEST(DpiSubroutineContext, TheImportsContextMayChangeAcrossTheBoundary) {
  EXPECT_TRUE(DpiImportContextMayChangeAcrossBoundary(true));
  EXPECT_FALSE(DpiImportContextMayChangeAcrossBoundary(false));
}

TEST(DpiSubroutineContext, UnwindingAcrossTheBoundaryIsUndefined) {
  EXPECT_TRUE(
      DpiBehaviorIsDefinedAcross(DpiBoundaryCrossing::kExportCallAndReturn));
  EXPECT_FALSE(DpiBehaviorIsDefinedAcross(
      DpiBoundaryCrossing::kUnwindingBySetjmpAndLongjmp));
}

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

TEST(DpiSubroutineContext, ANativeFunctionCallingTheExportReachesIt) {
  ExportedGInScope design;
  EXPECT_EQ(design.rt.CallExport("g", {}).AsInt(), 7);
}

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
