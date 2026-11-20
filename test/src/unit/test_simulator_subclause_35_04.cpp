#include <dlfcn.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <map>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_reported_error.h"
#include "simulator/dpi_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/lowerer.h"
#include "simulator/shared_library.h"

using namespace delta;

namespace {

DpiRtFunction MakeImport(const char* c_name, const char* sv_name) {
  DpiRtFunction func;
  func.c_name = c_name;
  func.sv_name = sv_name;
  return func;
}

DpiRtExport MakeExport(const char* c_name, const char* sv_name) {
  DpiRtExport exp;
  exp.c_name = c_name;
  exp.sv_name = sv_name;
  return exp;
}

TEST(DpiGlobalNameSpace, AnImportResolvesToTheSymbolItsLinkageNameNames) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  const auto* found = rt.FindImportByGlobalName("c_add");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->sv_name, "sv_add");
}

TEST(DpiGlobalNameSpace, AnImportWithNoLinkageNameResolvesUnderItsSvName) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("", "sv_plain"));
  EXPECT_NE(rt.FindImportByGlobalName("sv_plain"), nullptr);
}

TEST(DpiGlobalNameSpace, TheSystemVerilogNameIsNotAGlobalName) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  EXPECT_EQ(rt.FindImportByGlobalName("sv_add"), nullptr);
  EXPECT_NE(rt.FindImport("sv_add"), nullptr);
  EXPECT_EQ(rt.FindImport("c_add"), nullptr);
}

TEST(DpiGlobalNameSpace, TwoImportsNamingOneSubroutineResolveToOneSymbol) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  rt.RegisterImport(MakeImport("c_add", "sv_plus"));
  EXPECT_EQ(rt.ImportCount(), 2U);
  EXPECT_EQ(rt.GlobalNameCount(), 1U);
}

TEST(DpiGlobalNameSpace, TheFirstDeclarationOfASymbolIsTheOneItResolvesTo) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  rt.RegisterImport(MakeImport("c_add", "sv_plus"));
  const auto* found = rt.FindImportByGlobalName("c_add");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->sv_name, "sv_add");
}

TEST(DpiGlobalNameSpace, AnExportDefinesTheSymbolItsLinkageNameNames) {
  DpiRuntime rt;
  rt.RegisterExport(MakeExport("c_ready", "sv_ready"));
  const auto* found = rt.FindExportByGlobalName("c_ready");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->sv_name, "sv_ready");
  EXPECT_EQ(rt.FindExportByGlobalName("sv_ready"), nullptr);
}

TEST(DpiGlobalNameSpace, ImportsAndExportsResolveIntoOneNameSpace) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  rt.RegisterExport(MakeExport("c_ready", "sv_ready"));
  EXPECT_TRUE(rt.HasGlobalName("c_add"));
  EXPECT_TRUE(rt.HasGlobalName("c_ready"));
  EXPECT_EQ(rt.GlobalNameCount(), 2U);
}

TEST(DpiGlobalNameSpace, ANameNoDeclarationResolvedToIsNotInTheNameSpace) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  EXPECT_FALSE(rt.HasGlobalName("c_absent"));
  EXPECT_FALSE(rt.HasGlobalName("sv_add"));
}

int AddSeven(int a) { return a + 7; }

TEST(DpiImportBinding, TheCallReachesTheFunctionTheLinkageNameNames) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" add_seven = function int add7(input int a);\n"
      "  int r;\n"
      "  initial r = add7(35);\n"
      "endmodule\n",
      f, {{"add_seven", reinterpret_cast<void*>(&AddSeven)}},
      "subclause_35_04_linkage");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 42U);
}

TEST(DpiImportBinding, AnImportWithNoSymbolIsLeftForItsCallToReport) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int add7(input int a);\n"
      "  int r;\n"
      "  initial r = add7(35);\n"
      "endmodule\n",
      f, {}, "subclause_35_04_no_symbol", "deltahdl-no-such-compiler");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'add7' is bound to no foreign implementation", 4,
      "35.5.4"));
  EXPECT_TRUE(std::none_of(f.diag.Diagnostics().begin(),
                           f.diag.Diagnostics().end(), [](const Diagnostic& d) {
                             return d.message.find("could not be built") !=
                                    std::string::npos;
                           }));
}

TEST(DpiImportBinding, AFormalWithNoCLayoutHereIsNamedAtTheCall) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  function int two(); return 2; endfunction\n"
      "  import \"DPI-C\" function int sum_sized(input int a [two()]);\n"
      "  int arr [2] = '{1, 2};\n"
      "  int r;\n"
      "  initial r = sum_sized(arr);\n"
      "endmodule\n",
      f, {{"sum_sized", reinterpret_cast<void*>(&AddSeven)}},
      "subclause_35_04_no_layout");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported subroutine 'sum_sized' is bound to no "
                            "foreign implementation: deltahdl does not yet "
                            "lay out in C the type of its formal 'a'",
                            6, "35.5.4"));
}

TEST(DpiImportBinding, CallsTheCompilerCannotBuildLeaveTheImportsUnbound) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" add_seven = function int add7(input int a);\n"
      "  int r;\n"
      "  initial r = add7(35);\n"
      "endmodule\n",
      f, {{"add_seven", reinterpret_cast<void*>(&AddSeven)}},
      "subclause_35_04_no_compiler", "deltahdl-no-such-compiler");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the calls into C of the design's imported subroutines could not be "
      "built: 'deltahdl-no-such-compiler' did not build a shared library",
      0, ""));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported subroutine 'add7' is bound to no "
                            "foreign implementation: its call into C could "
                            "not be built",
                            4, "35.5.4"));
}

TEST(DpiImportBinding, TheRunFindsFunctionsALoadedLibraryDefines) {
  const SharedLibraryLoad kLibrary = BuildAndLoadCSharedLibrary(
      "int deltahdl_subclause_35_04_triple(int a) { return 3 * a; }\n",
      CallBuildDir("subclause_35_04_library"), "cc");
  ASSERT_NE(kLibrary.handle, nullptr) << kLibrary.error;
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" deltahdl_subclause_35_04_triple =\n"
      "      function int triple(input int a);\n"
      "  int r;\n"
      "  initial r = triple(7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  BindDesignDpiImports(f.ctx);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 21U);
}

TEST(DpiImportBinding, ARunWithNoImportBindsNothing) {
  SimFixture f;
  BindDesignDpiImports(f.ctx);
  EXPECT_EQ(f.ctx.GetDpiRuntime(), nullptr);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

uint64_t ValueAfterRun(const std::string& src,
                       const std::map<std::string, void*>& functions,
                       const char* dir, const char* var) {
  SimFixture f;
  RunWithImportsBound(src, f, functions, std::string("subclause_35_04_") + dir);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* found = f.ctx.FindVariable(var);
  return found == nullptr ? ~uint64_t{0} : found->value.ToUint64();
}

TEST(DpiImportBinding, AnImportWhoseSvNameIsNoCIdentifierReachesItsLinkage) {
  EXPECT_EQ(ValueAfterRun("module t;\n"
                          "  import \"DPI-C\" init_1 = function int \\init[1] "
                          "(input int a);\n"
                          "  int r;\n"
                          "  initial r = \\init[1] (35);\n"
                          "endmodule\n",
                          {{"init_1", reinterpret_cast<void*>(&AddSeven)}},
                          "escaped_sv_name", "r"),
            42U);
}

constexpr const char* kNativeAndImportOfOneName =
    "module t;\n"
    "  function int foo; return 1; endfunction\n"
    "  import \"DPI-C\" foo = function int bar(input int a);\n"
    "  int r, s;\n"
    "  initial begin r = foo(); s = bar(35); end\n"
    "endmodule\n";

TEST(DpiImportBinding, ANativeFunctionKeepsTheNameItsImportLinksUnder) {
  EXPECT_EQ(ValueAfterRun(kNativeAndImportOfOneName,
                          {{"foo", reinterpret_cast<void*>(&AddSeven)}},
                          "native_name_r", "r"),
            1U);
}

TEST(DpiImportBinding, AnImportLinkedUnderANativeFunctionsNameReachesC) {
  EXPECT_EQ(ValueAfterRun(kNativeAndImportOfOneName,
                          {{"foo", reinterpret_cast<void*>(&AddSeven)}},
                          "native_name_s", "s"),
            42U);
}

const char* exported_symbol = "";

int CallsExportedSymbol(int a) {
  auto exported =
      reinterpret_cast<int (*)(int)>(dlsym(RTLD_DEFAULT, exported_symbol));
  return exported == nullptr ? -1 : exported(a);
}

uint64_t ResultOfCallingTheFunctionExportAs(const char* symbol,
                                            const char* dir) {
  exported_symbol = symbol;
  return ValueAfterRun(
      "module t;\n"
      "  export \"DPI-C\" gname_fn = function sv_local_fn;\n"
      "  function int sv_local_fn(input int a); return a * 3; endfunction\n"
      "  import \"DPI-C\" context function int calls_exported_symbol("
      "input int a);\n"
      "  int r;\n"
      "  initial r = calls_exported_symbol(5);\n"
      "endmodule\n",
      {{"calls_exported_symbol",
        reinterpret_cast<void*>(&CallsExportedSymbol)}},
      dir, "r");
}

TEST(DpiExportLinkage, CReachesAFunctionExportByItsLinkageName) {
  EXPECT_EQ(ResultOfCallingTheFunctionExportAs("gname_fn", "export_gname"),
            15U);
}

TEST(DpiExportLinkage, CFindsNoFunctionExportUnderItsSvName) {
  EXPECT_EQ(ResultOfCallingTheFunctionExportAs("sv_local_fn", "export_svname"),
            0xFFFFFFFFU);
}

const char* exported_task_symbol = "";

int CallsExportedTask(int a) {
  auto exported =
      reinterpret_cast<int (*)(int)>(dlsym(RTLD_DEFAULT, exported_task_symbol));
  if (exported != nullptr) exported(a);
  return 0;
}

uint64_t CountAfterCallingTheTaskExportAs(const char* symbol, const char* dir) {
  exported_task_symbol = symbol;
  return ValueAfterRun(
      "module t;\n"
      "  export \"DPI-C\" bump_task_c = task bump;\n"
      "  int count;\n"
      "  task bump(input int a); count = count + a; endtask\n"
      "  import \"DPI-C\" context task calls_exported_task(input int a);\n"
      "  initial calls_exported_task(4);\n"
      "endmodule\n",
      {{"calls_exported_task", reinterpret_cast<void*>(&CallsExportedTask)}},
      dir, "count");
}

TEST(DpiExportLinkage, CReachesATaskExportByItsLinkageName) {
  EXPECT_EQ(CountAfterCallingTheTaskExportAs("bump_task_c", "task_gname"), 4U);
}

TEST(DpiExportLinkage, CFindsNoTaskExportUnderItsSvName) {
  EXPECT_EQ(CountAfterCallingTheTaskExportAs("bump", "task_svname"), 0U);
}

}  // namespace
