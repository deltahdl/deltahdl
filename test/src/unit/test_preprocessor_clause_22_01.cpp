#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, Clause22_1_DefineRecognized) {
  PreprocFixture f;
  Preprocess("`define MY_MACRO 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_UndefRecognized) {
  PreprocFixture f;
  Preprocess("`define FOO 1\n`undef FOO\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_UndefineallRecognized) {
  PreprocFixture f;
  Preprocess("`undefineall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_IfdefRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_IfndefRecognized) {
  PreprocFixture f;
  Preprocess("`ifndef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_ElseRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`else\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_ElsifRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`elsif UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_EndifRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_TimescaleRecognized) {
  PreprocFixture f;
  Preprocess("`timescale 1ns / 1ps\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_ResetallRecognized) {
  PreprocFixture f;
  Preprocess("`resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CelldefineRecognized) {
  PreprocFixture f;
  Preprocess("`celldefine\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_EndcelldefineRecognized) {
  PreprocFixture f;
  Preprocess("`endcelldefine\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_DefaultNettypeRecognized) {
  PreprocFixture f;
  Preprocess("`default_nettype wire\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_UnconnectedDriveRecognized) {
  PreprocFixture f;
  Preprocess("`unconnected_drive pull0\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_NounconnectedDriveRecognized) {
  PreprocFixture f;
  Preprocess("`nounconnected_drive\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_PragmaRecognized) {
  PreprocFixture f;
  Preprocess("`pragma protect begin\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_LineRecognized) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_BeginKeywordsRecognized) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\"\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_EndKeywordsRecognized) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\"\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_FileRecognized) {
  PreprocFixture f;
  auto result = Preprocess("int x = `__FILE__;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("<test>"), std::string::npos);
}

TEST(Preprocessor, Clause22_1_LineeMacroRecognized) {
  PreprocFixture f;
  Preprocess("int x = `__LINE__;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_define) {
  PreprocFixture f;
  Preprocess("`define define 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_undef) {
  PreprocFixture f;
  Preprocess("`define undef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_undefineall) {
  PreprocFixture f;
  Preprocess("`define undefineall 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_ifdef) {
  PreprocFixture f;
  Preprocess("`define ifdef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_ifndef) {
  PreprocFixture f;
  Preprocess("`define ifndef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_elsif) {
  PreprocFixture f;
  Preprocess("`define elsif 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_else) {
  PreprocFixture f;
  Preprocess("`define else 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_endif) {
  PreprocFixture f;
  Preprocess("`define endif 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_include) {
  PreprocFixture f;
  Preprocess("`define include 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_timescale) {
  PreprocFixture f;
  Preprocess("`define timescale 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_resetall) {
  PreprocFixture f;
  Preprocess("`define resetall 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_celldefine) {
  PreprocFixture f;
  Preprocess("`define celldefine 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_endcelldefine) {
  PreprocFixture f;
  Preprocess("`define endcelldefine 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_default_nettype) {
  PreprocFixture f;
  Preprocess("`define default_nettype 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_unconnected_drive) {
  PreprocFixture f;
  Preprocess("`define unconnected_drive 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_nounconnected_drive) {
  PreprocFixture f;
  Preprocess("`define nounconnected_drive 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_pragma) {
  PreprocFixture f;
  Preprocess("`define pragma 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_line) {
  PreprocFixture f;
  Preprocess("`define line 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_begin_keywords) {
  PreprocFixture f;
  Preprocess("`define begin_keywords 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_CannotRedefine_end_keywords) {
  PreprocFixture f;
  Preprocess("`define end_keywords 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_1_UserMacroNotConfusedWithDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_DIRECTIVE 42\n"
      "int x = `MY_DIRECTIVE;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, Clause22_1_IncludeWithAngleBrackets) {
  PreprocFixture f;

  Preprocess("`include <nonexistent.svh>\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}
