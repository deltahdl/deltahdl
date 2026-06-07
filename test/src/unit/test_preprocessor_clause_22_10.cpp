#include <gtest/gtest.h>

#include <algorithm>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

static bool IsTaggedAsCell(const Preprocessor& pp, const std::string& name) {
  const auto& cells = pp.CellModuleNames();
  return std::find(cells.begin(), cells.end(), name) != cells.end();
}

TEST(Preprocessor, Celldefine_Toggle) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}

TEST(Preprocessor, Endcelldefine_WithoutPrior_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

TEST(Preprocessor, Celldefine_NoPairing_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
}

TEST(Preprocessor, Celldefine_MostRecentWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
}

TEST(Preprocessor, Celldefine_MultiplePairs) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n`endcelldefine\n"
      "`celldefine\n`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

TEST(Preprocessor, Celldefine_InsideModule_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module t;\n`celldefine\nendmodule\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
}

TEST(Preprocessor, Endcelldefine_InsideModule_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\nmodule t;\n`endcelldefine\nendmodule\n", f,
                   pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

TEST(Preprocessor, Celldefine_NoOutput) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`celldefine\n", f, pp);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Endcelldefine_NoOutput) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`endcelldefine\n", f, pp);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Celldefine_TrailingContent) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`celldefine module m;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("module m;"), std::string::npos);
}

TEST(Preprocessor, Endcelldefine_TrailingContent) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`endcelldefine wire x;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire x;"), std::string::npos);
}

// §22.10: `celldefine/`endcelldefine tag modules as cell modules. A module
// declared between the two directives is recorded as a cell module.
TEST(Preprocessor, Celldefine_TagsModuleAsCell) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module cellmod;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "cellmod"));
}

// §22.10: the most recent occurrence of either directive controls whether
// modules are tagged. A module inside the `celldefine region is tagged; one
// declared after `endcelldefine is not.
TEST(Preprocessor, Celldefine_MostRecentControlsTagging) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "module incell;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "module outside;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "incell"));
  EXPECT_FALSE(IsTaggedAsCell(pp, "outside"));
}

// §22.10: `resetall includes the effects of an `endcelldefine directive, so a
// module declared after `resetall (while still textually inside a `celldefine
// region) is not tagged as a cell module.
TEST(Preprocessor, Resetall_IncludesEndcelldefine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "`resetall\n"
      "module afterreset;\n"
      "endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_FALSE(IsTaggedAsCell(pp, "afterreset"));
}

// §22.10: a macromodule declared between the directives is tagged as a cell
// module, just like a plain module.
TEST(Preprocessor, Celldefine_TagsMacromoduleAsCell) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "macromodule mm;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "mm"));
}

// §22.10: the directives tag modules specifically. A non-module design element
// (here an interface) declared inside a `celldefine region is not recorded as a
// cell module.
TEST(Preprocessor, Celldefine_TagsOnlyModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "interface iface;\n"
      "endinterface\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(IsTaggedAsCell(pp, "iface"));
}

// §22.10: the most recent occurrence controls tagging in either direction. A
// `celldefine following an `endcelldefine re-enables tagging, so a module
// declared after the second `celldefine is tagged as a cell module.
TEST(Preprocessor, Celldefine_ReenableTagsModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`celldefine\n"
      "`endcelldefine\n"
      "`celldefine\n"
      "module reenabled;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(IsTaggedAsCell(pp, "reenabled"));
}
