#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

// --- §22.10: Basic `celldefine / `endcelldefine toggle ---

TEST(Preprocessor, Celldefine_Toggle) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}

// --- §22.10: `celldefine sets state ---

TEST(Preprocessor, Celldefine_SetsState) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
}

// --- §22.10: `endcelldefine clears state ---

TEST(Preprocessor, Endcelldefine_ClearsState) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

// --- §22.10: `endcelldefine without prior `celldefine (no-op, no error) ---

TEST(Preprocessor, Endcelldefine_WithoutPrior_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

// --- §22.10: `celldefine without `endcelldefine (independent, no error) ---

TEST(Preprocessor, Celldefine_NoPairing_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
}

// --- §22.10: Most recent occurrence controls ---

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

// --- §22.10: Multiple pairs in single source ---

TEST(Preprocessor, Celldefine_MultiplePairs) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n`endcelldefine\n"
                   "`celldefine\n`endcelldefine\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

// --- §22.10: Directives may appear inside design elements (no error) ---

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
  PreprocessWithPP("`celldefine\nmodule t;\n`endcelldefine\nendmodule\n",
                   f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.InCelldefine());
}

// --- §22.10: Directive produces no output ---

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

// --- §22.10: Trailing content on same line passes through ---

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

// --- §22.10: `resetall includes effects of `endcelldefine ---

TEST(Preprocessor, Celldefine_ResetallClears) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}
