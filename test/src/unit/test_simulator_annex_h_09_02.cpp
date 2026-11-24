#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_dpi_scope_names.h"
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

TEST(QualifiedNameOfAContext, ANestedInstanceIsNamedInFull) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module leaf;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf u_leaf();\n"
      "endmodule\n"
      "module nest;\n"
      "  mid u_mid();\n"
      "endmodule\n",
      "annex_h_09_02_nested");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"nest.u_mid.u_leaf"}));
}

TEST(QualifiedNameOfAContext, ATopModuleIsNamedByItself) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module lone;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "endmodule\n",
      "annex_h_09_02_lone");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"lone"}));
}

TEST(QualifiedNameOfAContext, DISABLED_AConditionalGenerateBlockIsNamedInFull) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module leaf;\n"
      "  if (1) begin : g_blk\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "  end\n"
      "endmodule\n"
      "module cgen;\n"
      "  leaf u_mid();\n"
      "endmodule\n",
      "annex_h_09_02_conditional");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"cgen.u_mid.g_blk"}));
}

TEST(QualifiedNameOfAContext, DISABLED_ACaseGenerateBlockIsNamedInFull) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module kgen;\n"
      "  case (2)\n"
      "    1: begin : g_one end\n"
      "    2: begin : g_two\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      "annex_h_09_02_case");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"kgen.g_two"}));
}

TEST(QualifiedNameOfAContext,
     DISABLED_EachLoopGenerateBlockIsNamedWithItsIndex) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "module lgen;\n"
      "  for (genvar i = 4; i < 6; i++) begin : g\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial #i r = see_scope();\n"
      "  end\n"
      "endmodule\n",
      "annex_h_09_02_loop");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"lgen.g[4]", "lgen.g[5]"}));
}

TEST(QualifiedNameOfAContext, AnInterfaceInstanceIsNamedInFull) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "interface bus;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "endinterface\n"
      "module itop;\n"
      "  bus u_if();\n"
      "endmodule\n",
      "annex_h_09_02_interface");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"itop.u_if"}));
}

TEST(QualifiedNameOfAContext, AProgramInstanceIsNamedInFull) {
  const std::vector<std::string> kSeen = ScopeNamesOfRun(
      "program prog;\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial r = see_scope();\n"
      "endprogram\n"
      "module ptop;\n"
      "  prog u_p();\n"
      "endmodule\n",
      "annex_h_09_02_program");
  EXPECT_EQ(kSeen, (std::vector<std::string>{"ptop.u_p"}));
}

int CallPlaceExport(int a) {
  auto place_f = NamedExport<int (*)(int)>("place_f");
  return place_f == nullptr ? -1 : place_f(a) + 1;
}

int TakeTwenty(int a) { return a + 20; }

constexpr const char* kPairInAPlace =
    "    import \"DPI-C\" context function int call_place(input int a);\n"
    "    function int place_f(input int a); return a * 3; endfunction\n"
    "    export \"DPI-C\" function place_f;\n";

constexpr const char* kPlainImport =
    "  import \"DPI-C\" function int take(input int a);\n";

uint64_t PlaceResult(const std::string& src, const char* variable) {
  SimFixture f;
  RunDesignWithC(src, f,
                 {{"call_place", CAddress(&CallPlaceExport)},
                  {"take", CAddress(&TakeTwenty)}},
                 "annex_h_09_02_place");
  return DesignValue(f, variable);
}

std::string WithPair(const std::string& before, const std::string& after) {
  std::string src = before;
  src += kPairInAPlace;
  src += after;
  return src;
}

std::string WithImport(const std::string& before, const std::string& after) {
  std::string src = before;
  src += kPlainImport;
  src += after;
  return src;
}

TEST(PairDeclaredInAScope, AModulesPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("module t;\n",
                                 "  int r;\n"
                                 "  initial r = call_place(5);\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(PairDeclaredInAScope, DISABLED_AProgramsPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("program p;\n",
                                 "  int r;\n"
                                 "  initial r = call_place(5);\n"
                                 "endprogram\n"
                                 "module t;\n"
                                 "  p u();\n"
                                 "endmodule\n"),
                        "u.r"),
            16u);
}

TEST(PairDeclaredInAScope, DISABLED_AnInterfacesPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("interface i;\n",
                                 "  int r;\n"
                                 "  initial r = call_place(5);\n"
                                 "endinterface\n"
                                 "module t;\n"
                                 "  i u();\n"
                                 "endmodule\n"),
                        "u.r"),
            16u);
}

TEST(PairDeclaredInAScope, DISABLED_APackagesPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("package pk;\n",
                                 "endpackage\n"
                                 "module t;\n"
                                 "  int r;\n"
                                 "  initial r = pk::call_place(5);\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(PairDeclaredInAScope, DISABLED_TheCompilationUnitsPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("",
                                 "module t;\n"
                                 "  int r;\n"
                                 "  initial r = call_place(5);\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(PairDeclaredInAScope, AConditionalGenerateBlocksPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("module t;\n"
                                 "  int r;\n"
                                 "  if (1) begin : g\n",
                                 "    initial r = call_place(5);\n"
                                 "  end\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(PairDeclaredInAScope, ALoopGenerateBlocksPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("module t;\n"
                                 "  int r;\n"
                                 "  for (genvar i = 0; i < 1; i++) begin : g\n",
                                 "    initial r = call_place(5);\n"
                                 "  end\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(PairDeclaredInAScope, ACaseGenerateBlocksPairIsCalledBothWays) {
  EXPECT_EQ(PlaceResult(WithPair("module t;\n"
                                 "  int r;\n"
                                 "  case (1)\n"
                                 "    1: begin : g\n",
                                 "    initial r = call_place(5);\n"
                                 "    end\n"
                                 "  endcase\n"
                                 "endmodule\n"),
                        "r"),
            16u);
}

TEST(ImportDeclaredInAScope, AnInterfacesImportIsCalled) {
  EXPECT_EQ(PlaceResult(WithImport("interface i;\n",
                                   "  int r;\n"
                                   "  initial r = take(5);\n"
                                   "endinterface\n"
                                   "module t;\n"
                                   "  i u();\n"
                                   "endmodule\n"),
                        "u.r"),
            25u);
}

TEST(ImportDeclaredInAScope, APackagesImportIsCalled) {
  EXPECT_EQ(PlaceResult(WithImport("package pk;\n",
                                   "endpackage\n"
                                   "module t;\n"
                                   "  int r;\n"
                                   "  initial r = pk::take(5);\n"
                                   "endmodule\n"),
                        "r"),
            25u);
}

TEST(ImportDeclaredInAScope, TheCompilationUnitsImportIsCalled) {
  EXPECT_EQ(PlaceResult(WithImport("",
                                   "module t;\n"
                                   "  int r;\n"
                                   "  initial r = take(5);\n"
                                   "endmodule\n"),
                        "r"),
            25u);
}

TEST(ImportDeclaredInAScope, EachLoopGenerateBlocksImportIsCalled) {
  SimFixture f;
  RunDesignWithC(
      "module t;\n"
      "  int a, b;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    import \"DPI-C\" function int take(input int a);\n"
      "    if (i == 0) initial a = take(5);\n"
      "    else initial b = take(6);\n"
      "  end\n"
      "endmodule\n",
      f, {{"take", CAddress(&TakeTwenty)}}, "annex_h_09_02_loop_import");
  EXPECT_EQ(DesignValue(f, "a"), 25u);
  EXPECT_EQ(DesignValue(f, "b"), 26u);
}

int CallG() {
  auto g = NamedExport<int (*)()>("inst_g");
  return g == nullptr ? -1 : g();
}

int CallGTask() {
  auto g = NamedExport<int (*)(int*)>("inst_g_task");
  int seen = -1;
  if (g != nullptr) g(&seen);
  SeeInC({seen});
  return 0;
}

TEST(TransitiveContext, AnImportCallingTheExportMatchesANativeCaller) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  function int inst_g(); return v; endfunction\n"
      "  export \"DPI-C\" function inst_g;\n"
      "  import \"DPI-C\" context function int f_prime();\n"
      "  function int f(); return inst_g(); endfunction\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = f();\n"
      "    b = f_prime();\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "endmodule\n",
      f, {{"f_prime", CAddress(&CallG)}}, "annex_h_09_02_transitive");
  EXPECT_EQ(DesignValue(f, "u1.a"), 40u);
  EXPECT_EQ(DesignValue(f, "u1.b"), 40u);
  EXPECT_EQ(DesignValue(f, "u2.a"), 80u);
  EXPECT_EQ(DesignValue(f, "u2.b"), 80u);
}

TEST(TransitiveContext, DISABLED_AnImportCalledFromAnotherInstanceKeepsItsOwn) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  function int inst_g(); return v; endfunction\n"
      "  export \"DPI-C\" function inst_g;\n"
      "  import \"DPI-C\" context function int f_prime();\n"
      "endmodule\n"
      "module t;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    #1 a = u1.f_prime();\n"
      "    b = u2.f_prime();\n"
      "  end\n"
      "endmodule\n",
      f, {{"f_prime", CAddress(&CallG)}}, "annex_h_09_02_called_elsewhere");
  EXPECT_EQ(DesignValue(f, "a"), 40u);
  EXPECT_EQ(DesignValue(f, "b"), 80u);
}

TEST(TransitiveContext, DISABLED_AnImportedTaskEnablesTheExportOfItsInstance) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  task inst_g_task(output int o); o = v; endtask\n"
      "  export \"DPI-C\" task inst_g_task;\n"
      "  import \"DPI-C\" context task f_prime();\n"
      "  initial #ID f_prime();\n"
      "endmodule\n"
      "module t;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "endmodule\n",
      f, {{"f_prime", CAddress(&CallGTask)}}, "annex_h_09_02_task");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{40, 80}));
}

TEST(TransitiveContext, AnExportReenteredThroughAnImportKeepsItsInstance) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  int depth;\n"
      "  import \"DPI-C\" context function int f_prime();\n"
      "  function int inst_g();\n"
      "    depth++;\n"
      "    return depth < 3 ? f_prime() : v;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function inst_g;\n"
      "  int b;\n"
      "  initial b = f_prime();\n"
      "endmodule\n"
      "module t;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "endmodule\n",
      f, {{"f_prime", CAddress(&CallG)}}, "annex_h_09_02_reentered");
  EXPECT_EQ(DesignValue(f, "u1.b"), 40u);
  EXPECT_EQ(DesignValue(f, "u2.b"), 80u);
}

int FillFromInstance() {
  auto fill = NamedExport<void (*)(int*)>("inst_fill");
  int seen = -1;
  if (fill != nullptr) fill(&seen);
  return seen;
}

TEST(TransitiveContext, DISABLED_AnExportedFunctionOfAnInstanceFillsItsOutput) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  function void inst_fill(output int o); o = v; endfunction\n"
      "  export \"DPI-C\" function inst_fill;\n"
      "  import \"DPI-C\" context function int f_prime();\n"
      "  int b;\n"
      "  initial b = f_prime();\n"
      "endmodule\n"
      "module t;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "endmodule\n",
      f, {{"f_prime", CAddress(&FillFromInstance)}}, "annex_h_09_02_fill");
  EXPECT_EQ(DesignValue(f, "u1.b"), 40u);
  EXPECT_EQ(DesignValue(f, "u2.b"), 80u);
}

}  // namespace
