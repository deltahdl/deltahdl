#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh5Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh5Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh5Fixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ===========================================================================
// §5.3 White space — simulation-level tests
//
// LRM §5.3: "White space shall contain the characters for spaces, tabs,
// newlines, formfeeds, and end of file. These characters shall be ignored
// except when they serve to separate other lexical tokens. However, blanks
// and tabs shall be considered significant characters in string literals
// (see 5.9)."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Whitespace variations do not affect simulation results
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceSameResultWithSpaces) {
  // Normal spacing — compute a + b.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = a + b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(SimCh5, WhitespaceSameResultWithTabs) {
  // Tab-delimited tokens — identical computation must yield same result.
  auto result = RunAndGet(
      "module\tt\t;\n"
      "\tlogic\t[7:0]\ta\t,\tb\t,\tresult\t;\n"
      "\tinitial\tbegin\n"
      "\t\ta\t=\t8'd10\t;\n"
      "\t\tb\t=\t8'd20\t;\n"
      "\t\tresult\t=\ta\t+\tb\t;\n"
      "\tend\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(SimCh5, WhitespaceSameResultWithNewlines) {
  // Every token on its own line.
  auto result = RunAndGet(
      "module\n"
      "t\n"
      ";\n"
      "logic\n"
      "[7:0]\n"
      "result\n"
      ";\n"
      "initial\n"
      "result\n"
      "=\n"
      "8'd42\n"
      ";\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh5, WhitespaceSameResultMinimal) {
  // Minimal whitespace — only where needed to separate keywords/identifiers.
  auto result = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd55;endmodule", "result");
  EXPECT_EQ(result, 55u);
}

TEST(SimCh5, WhitespaceSameResultExcessive) {
  // Excessive whitespace everywhere.
  auto result = RunAndGet(
      "  \t\n  module   \t  t  \n  ;  \n"
      "  logic   [  7  :  0  ]   result  ;  \n"
      "  initial   result   =   8'd77   ;  \n"
      "  endmodule  \n\n  ",
      "result");
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 2. Formfeed in source does not affect simulation
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceFormfeedInSource) {
  // Formfeed characters between tokens — must parse and simulate identically.
  auto result = RunAndGet(
      "module t;\f"
      "logic [7:0] result;\f"
      "initial result = 8'd99;\f"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 3. Mixed whitespace in expressions does not affect evaluation
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceMixedInExpression) {
  // Various whitespace around operators in an expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, c, result;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    c = 8'd5;\n"
      "    result =  a \t + \n b  \f +  c ;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// ---------------------------------------------------------------------------
// 4. Whitespace around assignment operator
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceAroundAssignment) {
  // No whitespace around '=' — still valid.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd33;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

// ---------------------------------------------------------------------------
// 5. String literal preserves blanks and tabs (§5.3 + §5.9)
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceStringLiteralPreserved) {
  // §5.3: blanks and tabs are significant in string literals.
  // Assign a string with spaces to a wide variable and verify encoding.
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a b\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "a b" is 3 bytes: 'a'=0x61, ' '=0x20, 'b'=0x62
  // Stored MSB first: 0x61_20_62 = 6365282
  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);          // 'b'
  EXPECT_EQ((val >> 8) & 0xFF, 0x20u);   // ' '
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);  // 'a'
}

TEST(SimCh5, WhitespaceStringLiteralTabPreserved) {
  // §5.3: tabs are significant in string literals.
  // Use a literal tab character inside the SV string literal.
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a\tb\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "a<TAB>b" is 3 bytes: 'a'=0x61, '\t'=0x09, 'b'=0x62
  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);          // 'b'
  EXPECT_EQ((val >> 8) & 0xFF, 0x09u);   // '\t'
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);  // 'a'
}

// ---------------------------------------------------------------------------
// 6. Whitespace as token separator — keyword separation
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceSeparatesKeywords) {
  // Without space, "moduleendmodule" would not parse. Whitespace separates.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin result = 8'd1; end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

// ---------------------------------------------------------------------------
// 7. always_comb with various whitespace patterns
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceAlwaysCombWithFormfeed) {
  // Formfeed inside always_comb body.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd7;\n"
      "  always_comb begin\f"
      "    result = a + 8'd3;\f"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

// ---------------------------------------------------------------------------
// 8. Whitespace in concatenation expression
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceInConcatenation) {
  // Various whitespace around concatenation braces.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    result = { \t a \n , \f b \t };\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0xA5u);
}

// ---------------------------------------------------------------------------
// 9. Whitespace around conditional operator
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceAroundTernary) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1'b1 \t ? \n 8'd100 \f : \t 8'd200;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 100u);
}

// ---------------------------------------------------------------------------
// 10. Multiple statements with only whitespace between
// ---------------------------------------------------------------------------
TEST(SimCh5, WhitespaceMultipleStatements) {
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10; \t \n b = 8'd20; \f\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}

// ===========================================================================
// §5.2 Lexical tokens — simulation-level tests
//
// LRM §5.2: "SystemVerilog source text files shall be a stream of lexical
// tokens. A lexical token shall consist of one or more characters. The layout
// of tokens in a source file shall be free format; that is, spaces and
// newline characters shall not be syntactically significant other than being
// token separators, except for escaped identifiers (see 5.6.1)."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Free format layout — different arrangements produce same simulation
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenFreeFormatIdenticalResult) {
  // §5.2: Free format — compact vs spread layout yields same result.
  auto compact = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd42;endmodule", "result");
  auto spread = RunAndGet(
      "module\nt\n;\nlogic\n[7:0]\nresult\n;\ninitial\nresult\n=\n8'd42\n;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(compact, spread);
  EXPECT_EQ(compact, 42u);
}

// ---------------------------------------------------------------------------
// 2. Comments do not affect simulation results
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenCommentsDoNotAffectSimulation) {
  // §5.2: Comments are tokens consumed during lexing; they must not affect
  // simulation behavior.
  auto result = RunAndGet(
      "module /* block */ t; // line\n"
      "  logic [7:0] /* type */ result /* name */;\n"
      "  initial /* proc */ begin\n"
      "    result /* lhs */ = /* rhs */ 8'd88 /* val */;\n"
      "  end // done\n"
      "endmodule /* eof */\n",
      "result");
  EXPECT_EQ(result, 88u);
}

// ---------------------------------------------------------------------------
// 3. All token categories participate correctly in simulation
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenAllCategoriesInSimulation) {
  // §5.2: Keywords, identifiers, operators, numbers all affect behavior.
  // Keywords: module, logic, initial, begin, end, endmodule, if, else
  // Identifiers: t, a, b, result
  // Operators: =, >, ?, :
  // Numbers: 8'd10, 8'd20
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = (a > b) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 20u);
}

// ---------------------------------------------------------------------------
// 4. Expression spanning multiple lines (free format)
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenMultilineExpression) {
  // §5.2: Free format — a single expression can span multiple lines.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial\n"
      "    result\n"
      "      =\n"
      "        8'd3\n"
      "          +\n"
      "        8'd7\n"
      "      ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

// ---------------------------------------------------------------------------
// 5. Multiple statements on one line (free format)
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenMultipleStatementsOneLine) {
  // §5.2: Free format — multiple statements on one line.
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin a = 8'd1; b = 8'd2; c = a + b; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// 6. Block comment acts as token separator in simulation context
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenBlockCommentAsSeparator) {
  // §5.2: Block comments separate tokens, so "module/**/t" is valid.
  auto result = RunAndGet(
      "module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd66;"
      "endmodule",
      "result");
  EXPECT_EQ(result, 66u);
}

// ---------------------------------------------------------------------------
// 7. Line comment terminates at newline, next line is normal code
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenLineCommentTerminatesAtNewline) {
  // §5.2+§5.4: Line comment ends at newline; code on next line executes.
  auto result = RunAndGet(
      "module t; // this is a comment\n"
      "  logic [7:0] result; // another comment\n"
      "  initial result = 8'd44; // value\n"
      "endmodule // end\n",
      "result");
  EXPECT_EQ(result, 44u);
}

// ---------------------------------------------------------------------------
// 8. Free format with always_comb
// ---------------------------------------------------------------------------
TEST(SimCh5, LexicalTokenFreeFormatAlwaysComb) {
  // §5.2: Free format applies to all constructs including always_comb.
  auto result = RunAndGet(
      "module t; logic [7:0] a, result;\n"
      "initial a = 8'd5;\n"
      "always_comb result\n=\na\n+\n8'd10\n;\nendmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}

// ===========================================================================
// §5.4 Comments — simulation-level tests
//
// LRM §5.4: "SystemVerilog has two forms to introduce comments. A one-line
// comment shall start with the two characters // and end with a newline
// character. A block comment shall start with /* and end with */. Block
// comments shall not be nested. The one-line comment token // shall not have
// any special meaning inside a block comment, and the block comment tokens
// /* and */ shall not have any special meaning inside a one-line comment."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Line comments stripped — simulation produces correct result
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentLineCommentStripped) {
  // §5.4: One-line comment starts with // and ends with newline.
  auto result = RunAndGet(
      "module t; // module declaration\n"
      "  logic [7:0] result; // variable\n"
      "  initial result = 8'd77; // assignment\n"
      "endmodule // end\n",
      "result");
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 2. Block comments stripped — simulation produces correct result
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentBlockCommentStripped) {
  // §5.4: Block comment starts with /* and ends with */.
  auto result = RunAndGet(
      "module /* module */ t /* name */;\n"
      "  logic /* type */ [7:0] /* width */ result /* var */;\n"
      "  initial /* process */ result = /* assign */ 8'd55 /* val */;\n"
      "endmodule /* end */\n",
      "result");
  EXPECT_EQ(result, 55u);
}

// ---------------------------------------------------------------------------
// 3. Block comments not nested — first */ ends the comment
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentBlockNotNested) {
  // §5.4: "Block comments shall not be nested."
  // "/* outer /* inner */" ends at first */ — remaining code is active.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial /* outer /* inner */ result = 8'd33;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

// ---------------------------------------------------------------------------
// 4. // inside block comment has no special meaning
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentLineInsideBlockNoEffect) {
  // §5.4: "The one-line comment token // shall not have any special meaning
  // inside a block comment."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  /* // this is not a line comment\n"
      "     still inside block comment */\n"
      "  initial result = 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 5. /* and */ inside line comment have no special meaning
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentBlockInsideLineNoEffect) {
  // §5.4: "The block comment tokens /* and */ shall not have any special
  // meaning inside a one-line comment."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  // /* this does not start a block comment\n"
      "  initial result = 8'd22;\n"
      "  // */ this does not end a block comment\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 22u);
}

// ---------------------------------------------------------------------------
// 6. Mixed line and block comments in expressions
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentMixedInExpression) {
  // Both comment forms within an expression do not alter results.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10; // ten\n"
      "    b = /* twenty */ 8'd20;\n"
      "    result = a /* plus */ + /* b */ b; // sum\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

// ---------------------------------------------------------------------------
// 7. Multiline block comment spans code lines
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentMultilineBlockSpan) {
  // A block comment spanning multiple lines removes all enclosed text.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    /* This block comment\n"
      "       spans multiple\n"
      "       lines */\n"
      "    result = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

// ---------------------------------------------------------------------------
// 8. Block comment as token separator in simulation
// ---------------------------------------------------------------------------
TEST(SimCh5, CommentBlockAsSeparator) {
  // §5.4: Block comments serve as token separators, just like whitespace.
  auto result = RunAndGet(
      "module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd71;"
      "endmodule",
      "result");
  EXPECT_EQ(result, 71u);
}

// ===========================================================================
// §5.5 Operators — simulation-level tests
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Single-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorSingleCharInExpr) {
  // §5.5: Single-character operator (+) used in expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10 + 8'd20;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

// ---------------------------------------------------------------------------
// 2. Double-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorDoubleCharInExpr) {
  // §5.5: Double-character operator (<<) used in expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd1 << 3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

// ---------------------------------------------------------------------------
// 3. Triple-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorTripleCharInExpr) {
  // §5.5: Triple-character operator (<<<) — arithmetic left shift.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd3 <<< 2;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// ---------------------------------------------------------------------------
// 4. Unary operator to the left of operand
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorUnaryLeftOfOperand) {
  // §5.5: "Unary operators shall appear to the left of their operand."
  // Unary minus (-) appears to the left of its operand.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = -8'sd5;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result & 0xFF, 251u);
}

// ---------------------------------------------------------------------------
// 5. Binary operator between operands
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorBinaryBetweenOperands) {
  // §5.5: "Binary operators shall appear between their operands."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd50 - 8'd15;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 35u);
}

// ---------------------------------------------------------------------------
// 6. Conditional operator (two operator characters, three operands)
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorConditionalThreeOperands) {
  // §5.5: "A conditional operator shall have two operator characters
  //        that separate three operands."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// 7. Conditional operator — false branch
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorConditionalFalseBranch) {
  // §5.5: Conditional operator selects third operand when first is false.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 0 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 8. Multiple operator types in single expression
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorMixedInExpression) {
  // §5.5: Single- and double-character operators combined.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = (8'd3 + 8'd5) << 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 16u);
}

// ---------------------------------------------------------------------------
// 9. Unary negation operator
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorUnaryNegation) {
  // §5.5: Unary logical negation operator (!) to the left of operand.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = !1'b0;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

// ---------------------------------------------------------------------------
// 10. Operators without whitespace
// ---------------------------------------------------------------------------
TEST(SimCh5, OperatorNoWhitespace) {
  // §5.5: Operators work as token separators, no whitespace needed.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd7+8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

// ===========================================================================
// §5.6.1 Escaped identifiers — simulation-level tests
// ===========================================================================

TEST(SimCh5, EscapedIdentAsVariable) {
  // §5.6.1: Escaped identifiers can name variables.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\myvar ;\n"
      "  initial \\myvar = 8'd55;\n"
      "endmodule\n",
      "\\myvar");
  EXPECT_EQ(result, 55u);
}

TEST(SimCh5, EscapedIdentSpecialChars) {
  // §5.6.1: Escaped identifiers may include printable ASCII 33-126.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\data+bus ;\n"
      "  initial \\data+bus = 8'd77;\n"
      "endmodule\n",
      "\\data+bus");
  EXPECT_EQ(result, 77u);
}

TEST(SimCh5, EscapedKeywordAsVariable) {
  // §5.6.1: An escaped keyword is treated as a user-defined identifier.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\module ;\n"
      "  initial \\module = 8'd99;\n"
      "endmodule\n",
      "\\module");
  EXPECT_EQ(result, 99u);
}

TEST(SimCh5, EscapedIdentMultipleVars) {
  // §5.6.1: Multiple escaped identifiers in the same module.
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] \\a+b , \\c-d ;\n"
      "  initial begin\n"
      "    \\a+b = 8'd10;\n"
      "    \\c-d = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("\\a+b");
  auto* v2 = f.ctx.FindVariable("\\c-d");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
}

TEST(SimCh5, EscapedIdentInExpression) {
  // §5.6.1: Escaped identifiers used in expressions.
  SimCh5Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] \\x! , result;\n"
      "  initial begin\n"
      "    \\x! = 8'd6;\n"
      "    result = \\x! + 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}
