#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"

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

}  // namespace
