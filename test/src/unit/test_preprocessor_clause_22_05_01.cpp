#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// --- §22.5.1: Simple macro definition and substitution ---

TEST(Preprocessor, Clause22_5_1_SimpleDefineAndSubstitute) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WORDSIZE 8\n"
      "logic [1:`WORDSIZE] data;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("8"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_EmptyMacroBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EMPTY\n"
      "int x = `EMPTY;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Empty macro should substitute to nothing.
  EXPECT_NE(result.find("int x = ;"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_MacroRedefineLatestPrevails) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define VAL 1\n"
      "`define VAL 2\n"
      "int x = `VAL;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("2"), std::string::npos);
}

// --- §22.5.1: Compiler directive names cannot be redefined ---

TEST(Preprocessor, Clause22_5_1_RedefineCompilerDirectiveError) {
  PreprocFixture f;
  Preprocess("`define ifdef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_5_1_RedefineDefineError) {
  PreprocFixture f;
  Preprocess("`define define 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Clause22_5_1_RedefineIncludeError) {
  PreprocFixture f;
  Preprocess("`define include 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.5.1: Macro name can reuse ordinary identifiers ---

TEST(Preprocessor, Clause22_5_1_MacroNameReuseOrdinaryIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define data 42\n"
      "int data = `data;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `data and data are different.
  EXPECT_NE(result.find("int data = 42;"), std::string::npos);
}

// --- §22.5.1: Multi-line macro with backslash continuation ---

TEST(Preprocessor, Clause22_5_1_MultiLineBackslashContinuation) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MULTI a + \\\n"
      "b + \\\n"
      "c\n"
      "int x = `MULTI;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("a +"), std::string::npos);
  EXPECT_NE(result.find("b +"), std::string::npos);
  EXPECT_NE(result.find("c"), std::string::npos);
}

// --- §22.5.1: Unterminated string in macro body ---

TEST(Preprocessor, Clause22_5_1_UnterminatedStringInBody) {
  PreprocFixture f;
  Preprocess("`define BAD \"unterminated\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.5.1: Function-like macros ---

TEST(Preprocessor, Clause22_5_1_FunctionLikeMacroSingleArg) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define NAND(dly) nand #dly\n"
      "`NAND(2) g1 (q, a, b);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("nand #2"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_FunctionLikeMacroMultipleArgs) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define D(x,y) initial $display(\"start\", x , y, \"end\");\n"
      "`D( \"msg1\" , \"msg2\" )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"msg1\""), std::string::npos);
  EXPECT_NE(result.find("\"msg2\""), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_FunctionLikeMacroEmptyArgs) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define D(x,y) initial $display(x, y);\n"
      "`D(,)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Both args empty — substituted literally as empty.
  EXPECT_NE(result.find("initial $display(, );"), std::string::npos);
}

// --- §22.5.1: No space between macro name and opening paren ---

TEST(Preprocessor, Clause22_5_1_SpaceBetweenNameAndParenNotFunctionLike) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define NOT_FUNC (a, b)\n"
      "int x = `NOT_FUNC;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Space before ( means this is NOT function-like; body is "(a, b)".
  EXPECT_NE(result.find("(a, b)"), std::string::npos);
}

// --- §22.5.1: Default arguments ---

TEST(Preprocessor, Clause22_5_1_DefaultArgUsedWhenOmitted) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MACRO1(a=5,b=\"B\",c) $display(a,,b,,c);\n"
      "`MACRO1 ( , 2, 3 )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // a omitted → default 5; b = 2; c = 3.
  EXPECT_NE(result.find("$display(5,,2,,3);"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_DefaultArgMiddleOmitted) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MACRO1(a=5,b=\"B\",c) $display(a,,b,,c);\n"
      "`MACRO1 ( 1 , , 3 )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // a = 1; b omitted → default "B"; c = 3.
  EXPECT_NE(result.find("$display(1,,\"B\",,3);"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_DefaultArgLastOmittedNoDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MACRO1(a=5,b=\"B\",c) $display(a,,b,,c);\n"
      "`MACRO1 ( , 2, )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // a omitted → 5; b = 2; c omitted with no default → empty.
  EXPECT_NE(result.find("$display(5,,2,,);"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_TrailingArgsWithDefaultsFilled) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MACRO2(a=5, b, c=\"C\") $display(a,,b,,c);\n"
      "`MACRO2 (, 2)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // a omitted → 5; b = 2; c omitted → default "C".
  EXPECT_NE(result.find("$display(5,,2,,\"C\");"), std::string::npos);
}

// --- §22.5.1: Too few arguments without default is error ---

TEST(Preprocessor, Clause22_5_1_TooFewArgsNoDefaultError) {
  PreprocFixture f;
  Preprocess(
      "`define MACRO1(a=5,b=\"B\",c) $display(a,,b,,c);\n"
      "`MACRO1 ( 1 )\n",
      f);
  // b and c omitted; c has no default → error.
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.5.1: Too many arguments is error ---

TEST(Preprocessor, Clause22_5_1_TooManyArgsError) {
  PreprocFixture f;
  Preprocess(
      "`define D(x,y) x + y\n"
      "`D(1,2,3)\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.5.1: White space allowed between macro name and ( in usage ---

TEST(Preprocessor, Clause22_5_1_WhiteSpaceBetweenNameAndParenInUsage) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ADD(a,b) a + b\n"
      "int x = `ADD (1, 2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("1 + 2"), std::string::npos);
}

// --- §22.5.1: `" (backtick-quote) for string construction ---

TEST(Preprocessor, Clause22_5_1_BacktickQuoteStringConstruction) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MAKE_STR(x) `\"x`\"\n"
      "string s = `MAKE_STR(hello);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"hello\""), std::string::npos);
}

// --- §22.5.1: `\`" for escaped quote in macro string ---

TEST(Preprocessor, Clause22_5_1_BacktickEscapedQuote) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MSG(x,y) `\"x: `\\`\"y`\\`\"`\"\n"
      "$display(`MSG(left,right));\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"left: \\\"right\\\"\""), std::string::npos);
}

// --- §22.5.1: `` (double backtick) for token concatenation ---

TEST(Preprocessor, Clause22_5_1_TokenConcatenation) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define APPEND(f) f``_primary\n"
      "`APPEND(clock)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("clock_primary"), std::string::npos);
}

// --- §22.5.1: No substitution within string literals ---

TEST(Preprocessor, Clause22_5_1_NoSubstitutionInStringLiteral) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HI Hello\n"
      "$display(\"`HI, world\");\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `HI inside string literal should NOT be expanded.
  EXPECT_NE(result.find("`HI, world"), std::string::npos);
}

// --- §22.5.1: Macro text with other macro usages ---

TEST(Preprocessor, Clause22_5_1_MacroUsageInBodyExpandedAtUse) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 10\n"
      "`define B `A + 1\n"
      "int x = `B;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("10 + 1"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_MacroUsageExpandedAfterOuterSubstitution) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define INNER 42\n"
      "`define OUTER(x) x + `INNER\n"
      "int x = `OUTER(1);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("1 + 42"), std::string::npos);
}

// --- §22.5.1: Expression as actual argument (literal substitution) ---

TEST(Preprocessor, Clause22_5_1_ExpressionArgumentLiteralSubstitution) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MAX(a,b) ((a) > (b) ? (a) : (b))\n"
      "n = `MAX(p+q, r+s);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("((p+q) > (r+s) ? (p+q) : (r+s))"), std::string::npos);
}

// --- §22.5.1: Nested macro calls as arguments ---

TEST(Preprocessor, Clause22_5_1_NestedMacroCallsAsArguments) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define TOP(a,b) a + b\n"
      "`TOP( `TOP(b,1), `TOP(42,a) )\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Should expand to: b + 1 + 42 + a
  EXPECT_NE(result.find("b + 1 + 42 + a"), std::string::npos);
}

// --- §22.5.1: Directive in macro text processed on expansion ---

TEST(Preprocessor, Clause22_5_1_DirectiveInMacroTextProcessedOnExpansion) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`define SET_TS `timescale 1ns / 1ps\n"
                           "`SET_TS\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

// --- §22.5.1: Macro defined in inactive conditional not processed ---

TEST(Preprocessor, Clause22_5_1_DefineInInactiveConditionalSkipped) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF\n"
      "`define HIDDEN 99\n"
      "`endif\n"
      "`ifdef HIDDEN\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// --- §22.5.1: Macro used anywhere in compilation unit after definition ---

TEST(Preprocessor, Clause22_5_1_MacroUsedAcrossFiles) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid1 = f.mgr.AddFile("<file1>", "`define SHARED 77\n");
  pp.Preprocess(fid1);
  auto fid2 = f.mgr.AddFile("<file2>", "int x = `SHARED;\n");
  auto result = pp.Preprocess(fid2);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("77"), std::string::npos);
}

// --- §22.5.1: Predefined macros from config ---

TEST(Preprocessor, Clause22_5_1_CommandLineDefines) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"CMDLINE", "42"}};
  auto result = Preprocess("int x = `CMDLINE;\n", f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

// --- §22.5.1: Macro body with balanced parens in actual argument ---

TEST(Preprocessor, Clause22_5_1_BalancedParensInActualArgument) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define APPLY(f) f\n"
      "`APPLY(foo(1,2))\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("foo(1,2)"), std::string::npos);
}

// --- §22.5.1: Empty EMPTY macro trick for overriding non-empty default ---

TEST(Preprocessor, Clause22_5_1_EmptyMacroOverridesNonEmptyDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EMPTY\n"
      "`define M(a=5) val=a;\n"
      "`M(`EMPTY)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `EMPTY substituted for a, then expanded to nothing → val=;
  EXPECT_NE(result.find("val=;"), std::string::npos);
}

// --- §22.5.1: Comment in macro body not part of substituted text ---

TEST(Preprocessor, Clause22_5_1_LineCommentInBodyStripped) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42 // this is a comment\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
  // The comment text should not appear in the expanded output.
  EXPECT_EQ(result.find("this is a comment"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_BlockCommentInBodyStripped) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42 /* block comment */ + 1\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
  EXPECT_NE(result.find("+ 1"), std::string::npos);
  EXPECT_EQ(result.find("block comment"), std::string::npos);
}

// --- §22.5.1: Function-like macro with single empty arg (no default) ---

TEST(Preprocessor, Clause22_5_1_SingleEmptyArgNoDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WRAP(x) [x]\n"
      "`WRAP()\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("[]"), std::string::npos);
}

// --- §22.5.1: `define inside and outside design elements ---

TEST(Preprocessor, Clause22_5_1_DefineInsideModule) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "`define LOCAL 7\n"
      "int x = `LOCAL;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("7"), std::string::npos);
}

TEST(Preprocessor, Clause22_5_1_DefineOutsideModule) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define GLOBAL 8\n"
      "module m;\n"
      "int x = `GLOBAL;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("8"), std::string::npos);
}

// --- §22.5.1: resetall does not affect text macros ---

TEST(Preprocessor, Clause22_5_1_ResetallDoesNotAffectMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PERSIST 99\n"
      "`resetall\n"
      "int x = `PERSIST;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("99"), std::string::npos);
}
