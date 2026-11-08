#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <string>
#include <utility>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

static std::string WithoutWhitespace(std::string text) {
  text.erase(std::remove_if(text.begin(), text.end(),
                            [](unsigned char c) { return std::isspace(c); }),
             text.end());
  return text;
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyAtLineHeadTakesIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`OPB(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("if(((3)&1)&&(!(3)))begin"),
            std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyAtLineHeadSkipsIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define LEGACY\n"
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`OPB(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("if((!(3)))begin"),
            std::string::npos);
  EXPECT_EQ(WithoutWhitespace(result).find("&1"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyMidLineTakesIfndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB2(F) (`ifndef LEGACY (F)&1 `else 0 `endif)\n"
      "y = `OPB2(2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("y=((2)&1);"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInFunctionMacroBodyMidLineTakesElse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"LEGACY", "1"}};
  auto result = Preprocess(
      "`define OPB2(F) (`ifndef LEGACY (F)&1 `else 0 `endif)\n"
      "y = `OPB2(2);\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("y=(0);"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInObjectMacroBodyMidLineTakesIfdef) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x = `M;\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInObjectMacroBodyMidLineTakesElse) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=0;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalOpeningObjectMacroBodyAtLineHead) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int x =\n"
      "`M\n"
      ";\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intx=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInMacroBodyUsedByOuterMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPB(FLAG) if ( `ifndef LEGACY ((FLAG)&1) && `endif (!(FLAG)) )"
      " begin\n"
      "`define FIELD(FLAG) begin `OPB(FLAG) end end\n"
      "`FIELD(3)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(
      WithoutWhitespace(result).find("beginif(((3)&1)&&(!(3)))beginendend"),
      std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, ConditionalInMacroBodySeesDefineAfterDefinition) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M `ifdef A 1 `else 0 `endif\n"
      "int p = `M;\n"
      "`define A\n"
      "int q = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(WithoutWhitespace(result).find("intp=0;"), std::string::npos);
  EXPECT_NE(WithoutWhitespace(result).find("intq=1;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

TEST(Preprocessor, IfdefExprAndWithOnlyTheRightOperandDefined) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}};
  auto result =
      Preprocess("`ifdef (A && B)\nboth_defined\n`endif\n", f, std::move(cfg));
  EXPECT_EQ(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprParenthesizedOperandFollowedByAnOperator) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess("`ifdef ((A) && B)\nboth_defined\n`endif\n", f,
                           std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, ElsifInsideAnUncompiledBlockCompilesNothing) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"INNER", "1"}};
  auto result = Preprocess(
      "`ifdef OUTER\n"
      "`ifdef NONE\n"
      "`elsif INNER\n"
      "inner_group\n"
      "`endif\n"
      "`else\n"
      "outer_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("inner_group"), std::string::npos);
  EXPECT_NE(result.find("outer_else"), std::string::npos);
}

TEST(Preprocessor, DirectiveAfterABlockCommentCloses) {
  PreprocFixture f;
  auto result = Preprocess(
      "/* a\n"
      " b */ `define AFTER_COMMENT 1\n"
      "`ifdef AFTER_COMMENT\n"
      "defined_after_comment\n"
      "`endif\n"
      "`ifdef NONE\n"
      "/* c\n"
      " d */ text /* e\n"
      " `endif */ more\n"
      "`endif\n"
      "after_skipped\n"
      "`ifdef NONE\n"
      "/* f\n"
      " g */ `endif\n"
      "after_closed\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("defined_after_comment"), std::string::npos);
  EXPECT_EQ(result.find("more"), std::string::npos);
  EXPECT_NE(result.find("after_skipped"), std::string::npos);
  EXPECT_NE(result.find("after_closed"), std::string::npos);
}

TEST(Preprocessor, InlineConditionalHoldingAMacroNamedLikeEndif) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A\n"
      "`define endif_mark EM\n"
      "x `ifdef A `endif_mark `endif y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("EM"), std::string::npos);
  EXPECT_NE(result.find('y'), std::string::npos);
}

TEST(Preprocessor, MidLineIfdefClosedOnALaterLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "x `ifdef A inside_first\n"
      "inside_second\n"
      "`endif\n"
      "after\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('x'), std::string::npos);
  EXPECT_EQ(result.find("inside_first"), std::string::npos);
  EXPECT_EQ(result.find("inside_second"), std::string::npos);
  EXPECT_NE(result.find("after"), std::string::npos);
}

TEST(Preprocessor, NestedInlineConditionals) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A\n"
      "p `ifdef A `ifndef B not_b `endif `endif q\n"
      "r `ifdef A `ifdef B b `else else_b `endif `endif s\n"
      "t `ifdef ((A)) paren_a `endif u\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("not_b"), std::string::npos);
  EXPECT_NE(result.find("else_b"), std::string::npos);
  EXPECT_EQ(result.find(" b "), std::string::npos);
  EXPECT_NE(result.find("paren_a"), std::string::npos);
}
TEST(Preprocessor, IfdefExprImplicationChainAssociatesRightToLeft) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B -> C)\n"
      "chain_kept\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("chain_kept"), std::string::npos);
}

TEST(Preprocessor, IfdefExprImplicationAndEquivalenceShareALevel) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B <-> C)\n"
      "mixed_kept\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("mixed_kept"), std::string::npos);
}

TEST(Preprocessor, IfdefExprImplicationWithATrueLeftSideTakesItsRightSide) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A -> B -> C)\n"
      "right_true\n"
      "`endif\n"
      "`ifdef (A -> B)\n"
      "only_a\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("right_true"), std::string::npos);
  EXPECT_EQ(result.find("only_a"), std::string::npos);
}

TEST(Preprocessor, EndifWithoutIfdef) {
  PreprocFixture f;
  Preprocess("`endif\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`endif with no `ifdef or `ifndef open before it",
                            1, "22.6"));
}

TEST(Preprocessor, ElseWithoutIfdef) {
  PreprocFixture f;
  Preprocess("text\n`else\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`else with no `ifdef or `ifndef open before it", 2,
                            "22.6"));
}

TEST(Preprocessor, ElsifWithoutIfdef) {
  PreprocFixture f;
  Preprocess("`elsif A\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`elsif with no `ifdef or `ifndef open before it",
                            1, "22.6"));
}

TEST(Preprocessor, IfdefWithoutEndif) {
  PreprocFixture f;
  Preprocess("text\n`ifdef SOMETHING\ntext\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`ifdef or `ifndef with no closing `endif", 2,
                            "22.6"));
}

TEST(Preprocessor, ConditionalMissingItsConditionIsReported) {
  PreprocFixture f;
  Preprocess(
      "`ifdef\n"
      "`endif\n"
      "`ifndef\n"
      "`elsif\n"
      "`endif\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`ifdef is missing its condition", 1, "22.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`ifndef is missing its condition", 3, "22.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`elsif is missing its condition", 4, "22.6"));
}

TEST(Preprocessor, SecondElseIsReported) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", ""}};
  Preprocess(
      "`ifdef A\n"
      "a1\n"
      "`else\n"
      "a2\n"
      "`else\n"
      "a3\n"
      "`endif\n"
      "x `ifdef A b1 `else b2 `else b3 `endif y\n",
      f, cfg);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a second `else in one `ifdef or `ifndef", 5,
                            "22.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a second `else in one `ifdef or `ifndef", 8,
                            "22.6"));
}

TEST(Preprocessor, NegationOutsideParenthesesIsNoIfdefCondition) {
  PreprocFixture f;
  Preprocess(
      "`ifdef !A\n"
      "module taken_m; endmodule\n"
      "`endif\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'!A' after `ifdef is no ifdef_condition", 1,
                            "22.6"));
}

TEST(Preprocessor, MalformedIfdefExpressionIsReported) {
  for (const char* condition :
       {"(A & B)", "(A | B)", "(A - B)", "(A <- B)", "(A &&)", "()", "(A"}) {
    PreprocFixture f;
    Preprocess(std::string("`ifdef ") + condition + "\nx\n`endif\n", f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("malformed ifdef_macro_expression '") + condition + "'", 1,
        "22.6"))
        << condition;
  }
}

TEST(Preprocessor, WellFormedIfdefExpressionIsAccepted) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", ""}};
  auto out = Preprocess("`ifdef ((A) && !(B))\nkept\n`endif\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("kept"), std::string::npos) << out;
}

TEST(Preprocessor, UnclosedInlineIfdefExpressionIsReported) {
  PreprocFixture f;
  Preprocess("wire w = 1 `ifdef (A a `endif ;\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed ifdef_macro_expression '(A a `endif ;",
                            1, "22.6"));
}

TEST(Preprocessor, UnterminatedStringInAnIgnoredBlockIsReported) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NOT_DEFINED\n"
      "  \"unterminated\n"
      "`endif\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unterminated string literal",
                            2, "22.6"));
}

TEST(Preprocessor, WellFormedIgnoredBlockIsNotReported) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NOT_DEFINED\n"
      "  wire = = ;\n"
      "  \"continued \\\n"
      "  here\" \"with \\\" quote\" \\escaped\"id \"x\"\n"
      "  x = \"\"\"multi\n"
      "  line\"\"\" y;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}
