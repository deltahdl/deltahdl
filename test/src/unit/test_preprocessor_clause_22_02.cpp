#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// §22.2: All compiler directives are preceded by the grave accent (`) char.

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
  // Apostrophe should NOT trigger macro expansion.
  EXPECT_EQ(result.find("42"), std::string::npos);
  EXPECT_NE(result.find("'MY_MAC"), std::string::npos);
}

// §22.2: Directives are not recognized within comments.

TEST(Preprocessor, Clause22_2_DirectiveInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "// `define SHOULD_NOT_DEFINE 1\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);
  // The `define inside the comment should NOT create a macro.
  // `SHOULD_NOT_DEFINE should remain unexpanded.
  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_DirectiveInBlockCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "/* `define SHOULD_NOT_DEFINE 1 */\n"
      "int x = `SHOULD_NOT_DEFINE;\n",
      f);
  // The `define inside the block comment should NOT create a macro.
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
  // The `define on a line within a block comment should NOT create a macro.
  EXPECT_NE(result.find("`SHOULD_NOT_DEFINE"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroExpansionInLineCommentIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "int x = 1; // `FOO\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `FOO after // should NOT be expanded — "replaced" must not appear.
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
  // `FOO inside /* */ should NOT be expanded.
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
  // `define BAR inside block comment should NOT take effect.
  // `BAR should remain unexpanded in the output.
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
  // `resetall inside block comment should NOT reset the timescale.
  EXPECT_TRUE(pp.HasTimescale());
}

// §22.2: Directives are not recognized within string literals.

TEST(Preprocessor, Clause22_2_DirectiveInStringLiteralIgnored) {
  PreprocFixture f;
  auto result = Preprocess(
      "string s = \"`define FOO 1\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `define inside a string literal should NOT create a macro.
  EXPECT_NE(result.find("\"`define FOO 1\""), std::string::npos);
}

TEST(Preprocessor, Clause22_2_MacroInStringLiteralNotExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO replaced\n"
      "string s = \"text `FOO text\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `FOO inside a string should NOT be expanded.
  EXPECT_NE(result.find("`FOO"), std::string::npos);
}

// §22.2: Macro expansion shall occur within a compiler directive.

TEST(Preprocessor, Clause22_2_MacroExpansionWithinIncludeDirective) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"MY_FILE", "\"nonexistent.svh\""}};
  Preprocess("`include `MY_FILE\n", f, std::move(cfg));
  // File doesn't exist, but the macro should be expanded first.
  EXPECT_TRUE(f.diag.HasErrors());
}

// §22.2: Unless specified as supporting multiple lines, directives shall be
// all on one line.

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

// §22.2: Directive within conditional compilation block.

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
  // The timescale directive in the inactive branch should NOT be processed.
  EXPECT_FALSE(pp.HasTimescale());
}

// §22.2: Directive within macro text.

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

// §22.2: Scope of a directive extends across files in compilation unit.

TEST(Preprocessor, Clause22_2_DirectiveScopePersistsAcrossPreprocessCalls) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});

  auto fid1 = f.mgr.AddFile("<file1>", "`default_nettype none\n");
  pp.Preprocess(fid1);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  // Second file should see the directive from the first.
  auto fid2 = f.mgr.AddFile("<file2>", "module m; endmodule\n");
  pp.Preprocess(fid2);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

// §22.2: Comment-string interaction edge cases.

TEST(Preprocessor, Clause22_2_BlockCommentStartInStringNotAComment) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "string s = \"/*\";\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // /* inside string is not a comment, so `FOO should still expand.
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
  // // inside string is not a comment, so `FOO should still expand.
  EXPECT_NE(result.find("val"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_NestedBlockCommentsNotSupported) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO val\n"
      "/* outer /* inner */ int x = `FOO; */\n",
      f);
  // SystemVerilog does not support nested block comments.
  // The first */ ends the comment; `FOO after it expands; trailing */ is text.
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

// §22.2: Directive with defined end may be followed by element on same line.

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
  // §22.2: text after `endif should be preserved.
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
  // §22.2: text after `else should be preserved.
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
  // §22.2: text after `celldefine should be preserved.
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
  auto result = Preprocess(
      "`resetall int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterNounconnectedDriveOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`nounconnected_drive int x = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_2_CodeAfterUndefineallOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`undefineall int x = 1;\n",
      f);
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
  // Macro in text after `endif should be expanded.
  EXPECT_NE(result.find("42"), std::string::npos);
}

// §22.2: Directive superseded by another directive.

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

// §22.2: Macro expansion within `ifdef directive argument.

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

// §22.2: Single-line constraint — non-define directives on one line.

TEST(Preprocessor, Clause22_2_TimescaleOnSingleLine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`timescale 1ns / 1ps\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

// §22.2: Block comment ending mid-line, followed by directive.

TEST(Preprocessor, Clause22_2_BlockCommentEndFollowedByDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
      "/* comment */ `timescale 1ns / 1ps\n");
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

// §22.2: Escaped backtick in string literal.

TEST(Preprocessor, Clause22_2_EscapedBacktickInStringNotDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "string s = \"value is \\`FOO\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §22.2: Multiple directives on separate lines maintain correct scope.

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
