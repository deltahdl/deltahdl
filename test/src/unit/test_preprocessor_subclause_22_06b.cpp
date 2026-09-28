#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <string>
#include <utility>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// The substituted text keeps the blanks around each directive it once held, so
// the expected text is compared with every white-space character removed.
static std::string WithoutWhitespace(std::string text) {
  text.erase(std::remove_if(text.begin(), text.end(),
                            [](unsigned char c) { return std::isspace(c); }),
             text.end());
  return text;
}

// §22.6 lets the conditional compilation directives stand anywhere in the
// source description (printed page 712), and §22.5.1 has a compiler directive
// written in a macro's text take effect when the macro is used (printed page
// 710), so an `ifdef or `ifndef inside a macro body is evaluated at each usage
// against the defines in force there. The preprocessor once copied the
// directive text through into the output, where the lexer reported the
// backtick under §5.2. UVM's m_uvm_field_op_begin macro is the shape of the
// first group of cases.
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

// A body that opens with the conditional is text to evaluate, not a directive
// line to hand to the directive reader, when the usage heads a line.
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

// The UVM shape proper: the macro holding the conditional is used inside
// another macro's body, so the conditional is met while that body is expanded.
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

// The condition is read against the defines in force at the usage, not at the
// definition: a macro defined after the body is written still selects.
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

// §22.6 resolves the expression by §11.8's rules, so `&&` is false when its
// left operand is, whatever the right one is. Only the right one is defined
// here, which is the operand order IfdefExprAndFalse in the file beside this
// one does not take.
TEST(Preprocessor, IfdefExprAndWithOnlyTheRightOperandDefined) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}};
  auto result =
      Preprocess("`ifdef (A && B)\nboth_defined\n`endif\n", f, std::move(cfg));
  EXPECT_EQ(result.find("both_defined"), std::string::npos);
}

// A parenthesized operand is an ifdef_macro_expression of its own, and an
// operator may follow it: the parenthesis closes the inner expression without
// ending the outer one.
TEST(Preprocessor, IfdefExprParenthesizedOperandFollowedByAnOperator) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess("`ifdef ((A) && B)\nboth_defined\n`endif\n", f,
                           std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("both_defined"), std::string::npos);
}

// §22.6 compiles a nested block only where the enclosing one is compiled, so
// an `elsif whose condition holds still compiles nothing inside an outer
// `ifdef whose condition does not, and the outer `else is compiled instead.
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

// §22.6 hides a directive inside a comment, and only there: the text after the
// comment closes is source text again. In a compiled block a directive there
// takes effect; in a skipped block an `endif there closes the block, and other
// text there is read only for a comment it opens, which then hides the
// `endif on its line.
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

// Within one line, a usage of a macro whose name only begins with endif is a
// usage, not the `endif closing the conditional around it.
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

// An `ifdef after other text on a line whose `endif is on a later line is no
// conditional within the line, so its block runs over the lines up to that
// `endif and is dropped with them when its condition fails.
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

// Conditionals nest within one line as they do across lines: an inner
// `ifndef, and an inner `ifdef with an `else of its own, each select their
// own group inside the outer one, and a doubly parenthesized condition is the
// expression inside it.
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
// §22.6 resolves an ifdef expression by §11.8's rules, and the text beneath
// Table 11-2 in §11.3.2 has `->` associate right to left. With nothing
// defined, `A -> B -> C` is `A -> (B -> C)`, `0 -> 1`, which is 1 and keeps
// the block; folded left to right it was `(A -> B) -> C`, `1 -> 0`, and the
// block was skipped.
TEST(Preprocessor, IfdefExprImplicationChainAssociatesRightToLeft) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B -> C)\n"
      "chain_kept\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("chain_kept"), std::string::npos);
}

// Table 11-2 puts `->` and `<->` on one row, one precedence level, so
// `A -> B <-> C` is `A -> (B <-> C)`, `0 -> 1`, which is 1. With `<->` a level
// below `->` it was `(A -> B) <-> C`, `1 <-> 0`, and the block was skipped.
TEST(Preprocessor, IfdefExprImplicationAndEquivalenceShareALevel) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B <-> C)\n"
      "mixed_kept\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("mixed_kept"), std::string::npos);
}

// A control on the cases above: with A defined, `A -> B -> C` is
// `1 -> (0 -> 0)`, `1 -> 1`, and keeps its block, while `A -> B` is `1 -> 0`
// and skips its own, so reading every chain as true does not pass.
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
