#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, Clause22_2_GraveAccentRequiredForDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = `MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_ApostropheIsNotGraveAccent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = 'MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("42"), std::string::npos);
  EXPECT_NE(result.find("'MY_MAC"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "// `define SHOULD_NOT_DEFINE 1\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveInBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "/* `define SHOULD_NOT_DEFINE 1 */\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveInMultilineBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "/*\n"
      "`define SHOULD_NOT_DEFINE 1\n"
      "*/\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroExpansionInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = 1; // `FOO\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroBeforeLineCommentExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = `FOO; // comment\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroInInlineBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = 1; /* `FOO */ int y = 2;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_BlockCommentAcrossMultipleLines) {
  PreprocFixture f;
  auto result = Preprocess(
      "/*\n"
      "some text\n"
      "`define BAR bad\n"
      "*/\n"
      "int y = `BAR;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("`BAR"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_ResetallInBlockCommentIgnored) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`timescale 1ns / 1ps\n"
                           "/*\n"
                           "`resetall\n"
                           "*/\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_DirectiveInStringLiteralIgnored) {
  PreprocFixture f;
  auto result = Preprocess("string s = \"`define FOO 1\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("\"`define FOO 1\""), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroInStringLiteralNotExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "string s = \"text `FOO text\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("`FOO"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroExpansionWithinIncludeDirective) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_FILE", "\"nonexistent.svh\""}};
  Preprocess("`include `MY_FILE\n", f, std::move(cfg));

  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_2_DefineSupportsMultilineWithBackslash) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MULTI_LINE_MAC \\\n"
      "  line1 + \\\n"
      "  line2\n"
      "int x = `MULTI_LINE_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("line1"), std::string::npos);
  EXPECT_NE(result.find("line2"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveInConditionalBlock) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"USE_TIMESCALE", "1"}};
  auto result = Preprocess(
      "`ifdef USE_TIMESCALE\n"
      "`timescale 1ns / 1ps\n"
      "`endif\n",
      f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_2_DirectiveInInactiveConditionalBlockSkipped) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`ifdef UNDEFINED_MACRO\n"
                           "`timescale 1us / 1ns\n"
                           "`endif\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_FALSE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_DirectiveInMacroTextProcessedOnExpansion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`define SET_TIMESCALE `timescale 1ns / 1ps\n"
                           "`SET_TIMESCALE\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_DirectiveScopePersistsAcrossPreprocessCalls) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});

  auto fid1 = f.mgr.AddFile("<file1>", "`default_nettype none\n");
  pp.Preprocess(fid1);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  auto fid2 = f.mgr.AddFile("<file2>", "module m; endmodule\n");
  pp.Preprocess(fid2);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, Clause22_2_BlockCommentStartInStringNotAComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "string s = \"/*\";\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_LineCommentMarkerInStringNotAComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "string s = \"//\";\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_NestedBlockCommentsNotSupported) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "/* outer /* inner */ int x = `FOO; */\n",
      f);

  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_EmptyBlockComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "/**/ int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterEndifOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`ifdef FOO\n"
      "int a = 1;\n"
      "`endif int b = 2;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int a = 1"), std::string::npos);

  EXPECT_NE(result.find("int b = 2"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterElseOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF_MACRO\n"
      "int a = 1;\n"
      "`else int b = 2;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("int b = 2"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterCelldefineOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`celldefine module m;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("module m"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterEndcelldefineOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`celldefine\n"
      "module m; endmodule\n"
      "`endcelldefine int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterResetallOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`resetall int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterNounconnectedDriveOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`nounconnected_drive int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterUndefineallOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`undefineall int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroAfterEndifExpandedOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define VAL 42\n"
      "`ifdef VAL\n"
      "int a = 1;\n"
      "`endif int b = `VAL;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveSupersededByAnother) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "`default_nettype wire\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, Clause22_2_MacroExpansionWithinIfdefUsingMacroBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FEATURE_A 1\n"
      "`ifdef FEATURE_A\n"
      "int enabled = 1;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int enabled = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_TimescaleOnSingleLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_BlockCommentEndFollowedByDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "/* comment */ `timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_MultilineBlockCommentEndFollowedByDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "/*\n"
                           "multi-line comment\n"
                           "*/ `timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_EscapedBacktickInStringNotDirective) {
  PreprocFixture f;
  auto result = Preprocess("string s = \"value is \\`FOO\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_2_MultipleDirectivesScopeChaining) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "`celldefine\n"
                           "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_CodeAfterTimescaleOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / 1ps int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterDefaultNettypeOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_nettype none int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterUnconnectedDriveOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`unconnected_drive pull0 int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri0);
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterUndefOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`define FOO 1\n`undef FOO int x = 42;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 42"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterEndKeywordsOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1800-2023\"\n"
      "`end_keywords int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterBeginKeywordsOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1800-2023\" int x = 1;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroExpansionWithinTimescale) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_PREC", "1ps"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / `MY_PREC\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Clause22_2_MacroExpansionWithinDefaultNettype) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_TYPE", "none"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`default_nettype `MY_TYPE\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, Clause22_2_DirectiveInsideDirectiveArgIsError) {
  PreprocFixture f;
  Preprocess("`default_nettype `resetall\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_2_MacroInRemainderAfterDirectiveExpanded) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"VAL", "42"}};
  auto result =
      Preprocess("`default_nettype none int x = `VAL;\n", f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}
