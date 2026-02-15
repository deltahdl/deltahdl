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
