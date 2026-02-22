#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.6.12 Randsequence — randsequence_statement
// =============================================================================

// randsequence ( production_identifier ) production+ endsequence
TEST(ParserA612, RandsequenceStmtWithName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
}

// randsequence ( ) production+ endsequence — no production name
TEST(ParserA612, RandsequenceStmtNoName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      main : first;\n"
      "      first : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
}

// =============================================================================
// A.6.12 Randsequence — rs_production
// =============================================================================

// Production with return type: int P : ...;
TEST(ParserA612, RsProductionWithReturnType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      int main : gen;\n"
      "      gen : { return 42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Production with port list: P(int x) : ...;
TEST(ParserA612, RsProductionWithPorts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(5);\n"
      "      void gen(int x) : { $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_rule (multiple alternatives with |)
// =============================================================================

// Multiple rules separated by |
TEST(ParserA612, RsRuleMultipleAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a | b | c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_production_list
// =============================================================================

// Sequence of production items
TEST(ParserA612, RsProductionListSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rand join production list
TEST(ParserA612, RsProductionListRandJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join a b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rand join ( expression ) with bias
TEST(ParserA612, RsProductionListRandJoinWithExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join (1) a b c;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_weight_specification
// =============================================================================

// Weight as integral number
TEST(ParserA612, RsWeightIntegralNumber) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 3 | b := 7;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight as identifier
TEST(ParserA612, RsWeightIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  int w = 5;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := w | b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight as parenthesized expression
TEST(ParserA612, RsWeightParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := (2 + 3) | b := (1);\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_code_block
// =============================================================================

// Code block with data declaration and statement
TEST(ParserA612, RsCodeBlockWithDataDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { int x; x = 5; $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Weight with code block
TEST(ParserA612, RsWeightWithCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 5 { $display(\"chose a\"); }\n"
      "           | b := 3 { $display(\"chose b\"); };\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_prod (all alternatives)
// =============================================================================

// rs_prod as rs_production_item
TEST(ParserA612, RsProdAsProductionItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_code_block
TEST(ParserA612, RsProdAsCodeBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $display(\"inline\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_if_else
TEST(ParserA612, RsProdAsIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_repeat
TEST(ParserA612, RsProdAsRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(3) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_case
TEST(ParserA612, RsProdAsCase) {
  auto r = Parse(
      "module m;\n"
      "  int sel = 1;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (sel) 0: a; 1: b; default: c; endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_production_item
// =============================================================================

// Production item with arguments
TEST(ParserA612, RsProductionItemWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(1, 2);\n"
      "      void gen(int a, int b) : { $display(a + b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Production item bare (no arguments)
TEST(ParserA612, RsProductionItemBare) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_if_else
// =============================================================================

// if without else
TEST(ParserA612, RsIfOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// if with else
TEST(ParserA612, RsIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (0) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_repeat
// =============================================================================

// repeat with integral expression
TEST(ParserA612, RsRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(5) child;\n"
      "      child : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case
// =============================================================================

// Case with multiple items
TEST(ParserA612, RsCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0: a;\n"
      "               1: b;\n"
      "               2: c;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case_item
// =============================================================================

// Case item with comma-separated expressions
TEST(ParserA612, RsCaseItemCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0, 1: a;\n"
      "               2, 3: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Case item with default
TEST(ParserA612, RsCaseItemDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (99)\n"
      "               0: a;\n"
      "               default: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Default with colon (default :)
TEST(ParserA612, RsCaseItemDefaultColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0)\n"
      "               default : a;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — break and return within productions
// =============================================================================

// Break terminates randsequence
TEST(ParserA612, BreakInRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a { break; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Return aborts current production
TEST(ParserA612, ReturnInRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a { return; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — complex / combined constructs
// =============================================================================

// Multiple productions with mixed prods (if, repeat, code_block, items)
TEST(ParserA612, ComplexMixedProds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(2) step { $display(\"done\"); };\n"
      "      step : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Nested randsequence (randsequence inside code block)
TEST(ParserA612, NestedRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(outer)\n"
      "      outer : {\n"
      "        randsequence(inner)\n"
      "          inner : { ; };\n"
      "        endsequence\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
