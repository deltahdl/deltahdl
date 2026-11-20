#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

TEST(LibraryMapInclude, LoadsLibraryDeclarationFromMapFile) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map", "library rtlLib *.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "top.v").string()), "rtlLib");
}

TEST(LibraryMapInclude, IncludeMergesReferencedFile) {
  ScratchDir tmp;
  tmp.Write("sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "library topLib *.v;\n"
                       "include sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "topLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "y.sv").string()), "subLib");
}

TEST(LibraryMapInclude, RelativeIncludePathAnchorsToContainingFile) {
  ScratchDir tmp;
  auto sub_dir = tmp.dir / "subdir";
  fs::create_directories(sub_dir);
  tmp.Write("subdir/sub.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map", "include subdir/sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((sub_dir / "x.sv").string()), "subLib");
}

TEST(LibraryMapInclude, RelativeLibrarySpecAnchorsToContainingFile) {
  ScratchDir tmp;
  auto a_dir = tmp.dir / "a";
  fs::create_directories(a_dir);
  tmp.Write("a/sub.map", "library inner *.v;\n");
  auto top = tmp.Write("top.map", "include a/sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));

  EXPECT_EQ(m.LibraryForFile((a_dir / "x.v").string()), "inner");

  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "work");
}

TEST(LibraryMapInclude, NestedIncludesAccumulateAllDeclarations) {
  ScratchDir tmp;
  tmp.Write("c.map", "library cLib *.cv;\n");
  tmp.Write("b.map",
            "include c.map;\n"
            "library bLib *.bv;\n");
  auto top = tmp.Write("a.map",
                       "include b.map;\n"
                       "library aLib *.av;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.av").string()), "aLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.bv").string()), "bLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.cv").string()), "cLib");
}

TEST(LibraryMapInclude, CycleIsDetectedAndReported) {
  ScratchDir tmp;
  tmp.Write("a.map", "include b.map;\n");
  auto top = tmp.Write("b.map", "include a.map;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapInclude, MissingIncludeIsReported) {
  ScratchDir tmp;
  auto top = tmp.Write("top.map", "include nonexistent.map;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapInclude, NestedRelativeIncludeAnchorsToImmediateContainingFile) {
  ScratchDir tmp;
  auto sub_dir = tmp.dir / "sub";
  fs::create_directories(sub_dir);
  tmp.Write("sub/b.map", "library deep *.dv;\n");
  tmp.Write("sub/a.map", "include b.map;\n");
  auto top = tmp.Write("top.map", "include sub/a.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((sub_dir / "x.dv").string()), "deep");
}

TEST(LibraryMapInclude, StandardCommentSyntaxIsAcceptedInMapFile) {
  ScratchDir tmp;
  tmp.Write("sub.map",
            "// leading line comment in the included map\n"
            "library subLib *.sv;\n");
  auto top = tmp.Write("top.map",
                       "// top-level line comment\n"
                       "library topLib *.v; /* trailing block comment */\n"
                       "/* multi-line block\n"
                       "   comment before the include */\n"
                       "include sub.map;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "x.v").string()), "topLib");
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "y.sv").string()), "subLib");
}

TEST(LibraryMapInclude, NonPermittedConstructInMapFileIsRejected) {
  ScratchDir tmp;
  auto top = tmp.Write("top.map", "module m; endmodule\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(top, &errors));
  EXPECT_FALSE(errors.empty());
}

TEST(LibraryMapInclude, AbsoluteIncludePathIsHonoredAsGiven) {
  ScratchDir tmp;
  auto away_dir = tmp.dir / "elsewhere";
  fs::create_directories(away_dir);
  auto away = tmp.Write("elsewhere/abs.map", "library absLib *.av;\n");
  auto top = tmp.Write("top.map", "include " + away.string() + ";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((away_dir / "x.av").string()), "absLib");
}

TEST(LibraryMapInclude, IncludedDeclarationsTakeTheIncludesPlaceInTheOrder) {
  ScratchDir tmp;
  tmp.Write("gates.map", "library gateLib gates/*.v;\n");
  auto top = tmp.Write("main.map",
                       "library rtlLib rtl/*.v;\n"
                       "include gates.map;\n"
                       "library aLib a/*.v;\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  const std::vector<std::string_view> kExpected = {"rtlLib", "gateLib", "aLib"};
  EXPECT_EQ(m.LibraryDeclarationOrder(), kExpected);
}

TEST(LibraryMapInclude, QuotedIncludePathNamesTheFileItsBareSpellingNames) {
  ScratchDir tmp;
  fs::create_directories(tmp.dir / "sub");
  tmp.Write("sub/lib.map", "library subLib *.sv;\n");
  auto top = tmp.Write("top.map", "include \"sub/lib.map\";\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  EXPECT_EQ(m.LibraryForFile((tmp.dir / "sub" / "x.sv").string()), "subLib");
}

TEST(LibraryMapInclude, ConfigDeclaredInAMapFileIsKept) {
  ScratchDir tmp;
  auto top = tmp.Write("lib.map",
                       "library rtlLib *.v;\n"
                       "config cfg; design rtlLib.top; endconfig\n");
  LibraryMap m;
  ASSERT_TRUE(m.LoadMapFile(top));
  const std::vector<ConfigDecl*> kConfigs = m.DeclaredConfigs();
  ASSERT_EQ(kConfigs.size(), 1u);
  EXPECT_EQ(kConfigs[0]->name, "cfg");
  EXPECT_EQ(kConfigs[0]->library, "work");
  ASSERT_EQ(kConfigs[0]->design_cells.size(), 1u);
  EXPECT_EQ(kConfigs[0]->design_cells[0].cell, "top");
}

void ExpectRejectedAsLibraryText(const std::string& form) {
  auto r = ParseLibrary("library rtlLib *.v;\n" + form + "\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "expected library declaration, include statement, "
                            "config declaration, or ';'",
                            2, "33.3.1"))
      << form;
}

TEST(LibraryMapContents, PackageInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("package p; endpackage");
}

TEST(LibraryMapContents, InterfaceInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("interface i; endinterface");
}

TEST(LibraryMapContents, ProgramInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("program g; endprogram");
}

TEST(LibraryMapContents, PrimitiveInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText(
      "primitive u(output y, input a); table 0 : 1 ; endtable endprimitive");
}

TEST(LibraryMapContents, CheckerInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("checker c; endchecker");
}

TEST(LibraryMapContents, DefineDirectiveInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("`define W 1");
}

TEST(LibraryMapContents, TimescaleDirectiveInAMapFileIsRejected) {
  ExpectRejectedAsLibraryText("`timescale 1ns/1ps");
}

TEST(LibraryMapContents, IfdefAroundALibraryDeclarationIsRejected) {
  ExpectRejectedAsLibraryText(
      "`ifdef GATES\n"
      "library gateLib *.vg;\n"
      "`endif");
}

TEST(LibraryMapContents, ForbiddenFormInAnIncludedMapFileIsRejected) {
  ScratchDir tmp;
  auto inner = tmp.Write("inner.map", "package p; endpackage\n");
  auto outer = tmp.Write("outer.map",
                         "library rtlLib *.v;\n"
                         "include inner.map;\n");
  LibraryMap m;
  std::vector<std::string> errors;
  EXPECT_FALSE(m.LoadMapFile(outer, &errors));
  ASSERT_EQ(errors.size(), 1u);
  EXPECT_EQ(errors[0], "parse errors in library map file " +
                           fs::weakly_canonical(inner).string());
}

}  // namespace
