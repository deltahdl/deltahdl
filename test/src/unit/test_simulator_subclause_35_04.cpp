#include <gtest/gtest.h>

#include <algorithm>
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

// §35.4: "Every subroutine imported to SystemVerilog shall eventually resolve
// to a global symbol. Similarly, every subroutine exported from SystemVerilog
// defines a global symbol. Thus the tasks and functions imported to and
// exported from SystemVerilog have their own global name space of linkage
// names, different from compilation-unit scope name space." The cases below
// hold the runtime to that name space: the linkage name reaches the
// declaration, the SystemVerilog name does not, and the two name spaces answer
// independently.

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

// §35.4: "If a global name is not explicitly given, it shall be the same as the
// SystemVerilog subroutine name." A declaration carrying no linkage name of its
// own therefore still resolves to a global symbol.
TEST(DpiGlobalNameSpace, AnImportWithNoLinkageNameResolvesUnderItsSvName) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("", "sv_plain"));
  EXPECT_NE(rt.FindImportByGlobalName("sv_plain"), nullptr);
}

// §35.4: the global name space is "different from compilation-unit scope name
// space", so the name SystemVerilog calls a subroutine by is not a global name
// once the declaration gives one. The import below is reachable by both names,
// each through the lookup belonging to its own name space, and by neither
// through the other's.
TEST(DpiGlobalNameSpace, TheSystemVerilogNameIsNotAGlobalName) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  EXPECT_EQ(rt.FindImportByGlobalName("sv_add"), nullptr);
  EXPECT_NE(rt.FindImport("sv_add"), nullptr);
  EXPECT_EQ(rt.FindImport("c_add"), nullptr);
}

// §35.4: "The same global subroutine can be referred to in multiple import
// declarations in different scopes or/and with different SystemVerilog names."
// Two such declarations name one symbol, so the name space holds one entry
// while the import registry holds two.
TEST(DpiGlobalNameSpace, TwoImportsNamingOneSubroutineResolveToOneSymbol) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  rt.RegisterImport(MakeImport("c_add", "sv_plus"));
  EXPECT_EQ(rt.ImportCount(), 2U);
  EXPECT_EQ(rt.GlobalNameCount(), 1U);
}

// §35.4: where several declarations refer to one global subroutine, the symbol
// is the one the first of them resolved to; a later reference to it does not
// stand for a second symbol that could replace the first.
TEST(DpiGlobalNameSpace, TheFirstDeclarationOfASymbolIsTheOneItResolvesTo) {
  DpiRuntime rt;
  rt.RegisterImport(MakeImport("c_add", "sv_add"));
  rt.RegisterImport(MakeImport("c_add", "sv_plus"));
  const auto* found = rt.FindImportByGlobalName("c_add");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->sv_name, "sv_add");
}

// §35.4: "every subroutine exported from SystemVerilog defines a global
// symbol", under the same defaulting rule imports follow.
TEST(DpiGlobalNameSpace, AnExportDefinesTheSymbolItsLinkageNameNames) {
  DpiRuntime rt;
  rt.RegisterExport(MakeExport("c_ready", "sv_ready"));
  const auto* found = rt.FindExportByGlobalName("c_ready");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->sv_name, "sv_ready");
  EXPECT_EQ(rt.FindExportByGlobalName("sv_ready"), nullptr);
}

// §35.4: imports and exports have "their own global name space" — one name
// space between them rather than one each — so it answers for a name either
// kind of declaration resolved to.
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

// The C function the imports below are bound to.
int AddSeven(int a) { return a + 7; }

// §35.4: an import resolves to the global symbol its linkage name names -- the
// c_identifier where the declaration gives one -- and a call reaches the
// function defined under that name. The SystemVerilog name `add7` names no
// function here, so a binding looking it up would find nothing.
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

// §35.5.4: an import no loaded code defines a symbol for stays unbound, and
// only its call is reported; nothing is built for it, so a C compiler that
// cannot be run goes unnoticed.
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

// §35.4 with §35.5.6.1: an import whose symbol is found but whose formal is
// an array sized by a constant function call, whose bound this simulator does
// not fold for the C layout yet, is left unbound, and its call's report says
// why.
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

// A binding whose calls the C compiler cannot build is reported with what the
// compiler said, and leaves every import it was building for unbound, each
// call saying so.
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

// §35.4 with Annex J: the run looks each linkage name up among the global
// symbols of the process, where a library loaded with its symbols global puts
// the functions it defines.
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

// A design that declares no import has no registry and nothing to bind.
TEST(DpiImportBinding, ARunWithNoImportBindsNothing) {
  SimFixture f;
  BindDesignDpiImports(f.ctx);
  EXPECT_EQ(f.ctx.GetDpiRuntime(), nullptr);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
