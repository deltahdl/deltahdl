#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, DirectiveInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "// `define SHOULD_NOT_DEFINE 1\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, DirectiveInBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "/* `define SHOULD_NOT_DEFINE 1 */\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, DirectiveInMultilineBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "/*\n"
      "`define SHOULD_NOT_DEFINE 1\n"
      "*/\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);

  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, MacroExpansionInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = 1; // `FOO\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, MacroBeforeLineCommentExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = `FOO; // comment\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, MacroInInlineBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = 1; /* `FOO */ int y = 2;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("replaced"), std::string::npos);
}

TEST(Preprocessor, BlockCommentAcrossMultipleLines) {
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

TEST(Preprocessor, ResetallInBlockCommentIgnored) {
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

TEST(Preprocessor, DirectiveInStringLiteralIgnored) {
  PreprocFixture f;
  auto result = Preprocess("string s = \"`define FOO 1\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("\"`define FOO 1\""), std::string::npos);
}

TEST(Preprocessor, MacroInStringLiteralNotExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "string s = \"text `FOO text\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("`FOO"), std::string::npos);
}

TEST(Preprocessor, MacroExpansionWithinIncludeDirective) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_FILE", "\"nonexistent.svh\""}};
  Preprocess("`include `MY_FILE\n", f, std::move(cfg));

  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefineSupportsMultilineWithBackslash) {
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

TEST(Preprocessor, DirectiveInConditionalBlock) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"USE_TIMESCALE", "1"}};
  Preprocess(
      "`ifdef USE_TIMESCALE\n"
      "`timescale 1ns / 1ps\n"
      "`endif\n",
      f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, DirectiveInInactiveConditionalBlockSkipped) {
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

TEST(Preprocessor, DirectiveInMacroTextProcessedOnExpansion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`define SET_TIMESCALE `timescale 1ns / 1ps\n"
                           "`SET_TIMESCALE\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, BlockCommentStartInStringNotAComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "string s = \"/*\";\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, LineCommentMarkerInStringNotAComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "string s = \"//\";\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, CodeAfterEndifOnSameLine) {
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

TEST(Preprocessor, CodeAfterElseOnSameLine) {
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

TEST(Preprocessor, CodeAfterCelldefineOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`celldefine module m;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("module m"), std::string::npos);
}

TEST(Preprocessor, CodeAfterEndcelldefineOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`celldefine\n"
      "module m; endmodule\n"
      "`endcelldefine int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterResetallOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`resetall int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterNounconnectedDriveOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`nounconnected_drive int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterUndefineallOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`undefineall int x = 1;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, MacroAfterEndifExpandedOnSameLine) {
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

TEST(Preprocessor, MacroExpansionWithinIfdefUsingMacroBody) {
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

TEST(Preprocessor, TimescaleOnSingleLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, BlockCommentEndFollowedByDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "/* comment */ `timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, MultilineBlockCommentEndFollowedByDirective) {
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

TEST(Preprocessor, CodeAfterTimescaleOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / 1ps int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterDefaultNettypeOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_nettype none int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterUnconnectedDriveOnSameLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`unconnected_drive pull0 int x = 1;\n");
  auto result = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri0);
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterUndefOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`define FOO 1\n`undef FOO int x = 42;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 42"), std::string::npos);
}

TEST(Preprocessor, CodeAfterEndKeywordsOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1800-2023\"\n"
      "`end_keywords int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, CodeAfterBeginKeywordsOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1800-2023\" int x = 1;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, MacroExpansionWithinTimescale) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_PREC", "1ps"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / `MY_PREC\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, MacroExpansionWithinDefaultNettype) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_TYPE", "none"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`default_nettype `MY_TYPE\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DirectiveInsideDirectiveArgIsError) {
  PreprocFixture f;
  Preprocess("`default_nettype `resetall\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, MacroInRemainderAfterDirectiveExpanded) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"VAL", "42"}};
  auto result =
      Preprocess("`default_nettype none int x = `VAL;\n", f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, GraveAccentRequiredForDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = `MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, ApostropheIsNotGraveAccent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_MAC 42\n"
      "int x = 'MY_MAC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("42"), std::string::npos);
  EXPECT_NE(result.find("'MY_MAC"), std::string::npos);
}

TEST(Preprocessor, EscapedBacktickInStringNotDirective) {
  PreprocFixture f;
  Preprocess("string s = \"value is \\`FOO\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, DirectiveTakesEffectImmediately) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "`default_nettype wire\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, MultipleDirectivesAllInEffect) {
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

TEST(Preprocessor, DirectivePersistsAcrossFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});

  auto fid1 = f.mgr.AddFile("<file1>", "`default_nettype none\n");
  pp.Preprocess(fid1);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  auto fid2 = f.mgr.AddFile("<file2>", "module m; endmodule\n");
  pp.Preprocess(fid2);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DirectiveInRemainderOfAnotherDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`celldefine `timescale 1ns / 1ps\n"
                           "module m; endmodule\n"
                           "`endcelldefine\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, DirectiveAtEndOfFileWithoutNewline) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_nettype none");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, MacroUsageInDirectiveArgIsNotADirective) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"NET", "none"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`default_nettype `NET\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DirectiveInNestedConditionalBlocks) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"OUTER", "1"}, {"INNER", "1"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>",
                           "`ifdef OUTER\n"
                           "`ifdef INNER\n"
                           "`timescale 1ns / 1ps\n"
                           "`endif\n"
                           "`endif\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, DirectiveInNestedConditionalInnerUndefined) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"OUTER", "1"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>",
                           "`ifdef OUTER\n"
                           "`ifdef INNER\n"
                           "`timescale 1ns / 1ps\n"
                           "`endif\n"
                           "`endif\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasTimescale());
}

TEST(Preprocessor, DirectiveInElseBranchProcessed) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`ifdef UNDEFINED\n"
                           "`default_nettype wire\n"
                           "`else\n"
                           "`default_nettype none\n"
                           "`endif\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DirectiveSupersededAcrossFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});

  auto fid1 = f.mgr.AddFile("<file1>", "`default_nettype none\n");
  pp.Preprocess(fid1);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  auto fid2 = f.mgr.AddFile("<file2>", "`default_nettype wire\n");
  pp.Preprocess(fid2);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, MacroExpansionWithinUnconnectedDrive) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"PULL", "pull1"}};
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto fid = f.mgr.AddFile("<test>", "`unconnected_drive `PULL\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
}

TEST(Preprocessor, WhitespaceOnlyBeforeDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "   \t  `default_nettype none\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, EmptyLinesBetweenDirectives) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`celldefine\n"
                           "\n"
                           "\n"
                           "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.InCelldefine());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, DirectiveInMacroTextInConditionalBlock) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"FEATURE", "1"}};
  auto result = Preprocess(
      "`define SET_TS `timescale 1ns / 1ps\n"
      "`ifdef FEATURE\n"
      "`SET_TS\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
}
