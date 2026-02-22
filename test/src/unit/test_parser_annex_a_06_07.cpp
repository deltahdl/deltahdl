#include <gtest/gtest.h>

#include <string>

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
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.7 Case statements
// =============================================================================

// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case_keyword ( case_expression )
//     case_item { case_item } endcase
// ---------------------------------------------------------------------------

// §12.5: basic case statement with single items
TEST(ParserA607, CaseStmtParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) 0: y = 1; default: y = 0; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
}

// §12.5: case statement items count and default detection
TEST(ParserA607, CaseStmtItems) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) 0: y = 1; default: y = 0; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

// §12.5: multiple case_item_expressions per case item (comma-separated)
TEST(ParserA607, CaseMultipleItemExprs) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(sel)\n"
                 "      0, 1: x = 8'd10;\n"
                 "      2, 3, 4: x = 8'd20;\n"
                 "      default: x = 8'd30;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 2u);
  EXPECT_EQ(stmt->case_items[1].patterns.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

// §12.5: default without colon
TEST(ParserA607, CaseDefaultNoColon) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) 0: y = 1; default y = 0; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

// §12.5: case with no default
TEST(ParserA607, CaseNoDefault) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) 0: y = 1; 1: y = 2; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_FALSE(stmt->case_items[1].is_default);
}

// §12.5: case with block statement in item body
TEST(ParserA607, CaseItemWithBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x)\n"
                 "      0: begin y = 1; z = 2; end\n"
                 "      default: begin y = 0; z = 0; end\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlock);
}

// ---------------------------------------------------------------------------
// case_keyword ::= case | casez | casex
// ---------------------------------------------------------------------------

// §12.5.1: casez keyword
TEST(ParserA607, CasezKeyword) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    casez(sel) 3'b1??: x = 1; default: x = 0; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

// §12.5.1: casex keyword
TEST(ParserA607, CasexKeyword) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    casex(sel) 3'b1??: x = 1; default: x = 0; endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
}

// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case ( case_expression ) inside
//     case_inside_item { case_inside_item } endcase
// ---------------------------------------------------------------------------

// §12.5.4: case-inside variant
TEST(ParserA607, CaseInsideParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) inside\n"
                 "      1, 3: y = 8'd10;\n"
                 "      [4:7]: y = 8'd20;\n"
                 "      default: y = 8'd30;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  EXPECT_TRUE(stmt->case_inside);
}

// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case_keyword ( case_expression ) matches
//     case_pattern_item { case_pattern_item } endcase
// ---------------------------------------------------------------------------

// §12.6.1: case-matches variant
TEST(ParserA607, CaseMatchesParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(v) matches\n"
                 "      5: y = 8'd10;\n"
                 "      default: y = 8'd20;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

// ---------------------------------------------------------------------------
// unique_priority with case
// ---------------------------------------------------------------------------

// §12.5.3: unique case
TEST(ParserA607, UniqueCaseParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    unique case(x)\n"
                 "      0: y = 1;\n"
                 "      1: y = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// §12.5.3: unique0 case
TEST(ParserA607, Unique0CaseParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    unique0 case(x)\n"
                 "      0: y = 1;\n"
                 "      1: y = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// §12.5.3: priority case
TEST(ParserA607, PriorityCaseParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    priority case(x)\n"
                 "      0: y = 1;\n"
                 "      1: y = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// §12.5.3: priority casez
TEST(ParserA607, PriorityCasezParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    priority casez(a)\n"
                 "      3'b00?: y = 1;\n"
                 "      3'b0??: y = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

// §12.5.2: constant expression as case_expression
TEST(ParserA607, ConstExprCaseExpr) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(1)\n"
                 "      a: y = 1;\n"
                 "      b: y = 2;\n"
                 "      default: y = 3;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_NE(stmt->condition, nullptr);
}

// §12.5: nested case statements
TEST(ParserA607, NestedCaseStmt) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(a)\n"
                 "      0: case(b)\n"
                 "           0: x = 1;\n"
                 "           1: x = 2;\n"
                 "         endcase\n"
                 "      1: x = 3;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kCase);
}

// ---------------------------------------------------------------------------
// case_inside_item ::=
//   range_list : statement_or_null
// range_list ::= value_range { , value_range }
// ---------------------------------------------------------------------------

// §12.5.4: case inside with range [lo:hi]
TEST(ParserA607, CaseInsideRange) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) inside\n"
                 "      [0:3]: y = 1;\n"
                 "      [4:7]: y = 2;\n"
                 "      default: y = 3;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  ASSERT_GE(stmt->case_items.size(), 2u);
}

// §12.5.4: case inside with multiple value_ranges (comma-separated)
TEST(ParserA607, CaseInsideMultipleRanges) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) inside\n"
                 "      1, 3, [5:7]: y = 1;\n"
                 "      default: y = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_inside);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
}

// ---------------------------------------------------------------------------
// randcase_statement ::= randcase randcase_item { randcase_item } endcase
// randcase_item ::= expression : statement_or_null
// ---------------------------------------------------------------------------

// §18.16: randcase statement
TEST(ParserA607, RandcaseParse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    randcase\n"
                 "      50: x = 1;\n"
                 "      30: x = 2;\n"
                 "      20: x = 3;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 3u);
}

// §18.16: randcase with block bodies
TEST(ParserA607, RandcaseWithBlocks) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    randcase\n"
                 "      50: begin x = 1; y = 2; end\n"
                 "      50: begin x = 3; y = 4; end\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 2u);
}

// ---------------------------------------------------------------------------
// value_range ::= expression
// value_range ::= [ expression : expression ]
// ---------------------------------------------------------------------------

// §11.4.13: value_range as simple expression in case-inside
TEST(ParserA607, ValueRangeExpression) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) inside\n"
                 "      5: y = 1;\n"
                 "      10: y = 2;\n"
                 "      default: y = 3;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §11.4.13: value_range with bracket range [lo:hi]
TEST(ParserA607, ValueRangeBracket) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x) inside\n"
                 "      [0:15]: y = 1;\n"
                 "      default: y = 0;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.5: case with null statement body (;)
TEST(ParserA607, CaseItemNullBody) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(x)\n"
                 "      0: ;\n"
                 "      1: y = 1;\n"
                 "      default: ;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// §12.5: case with expression as case_expression (not just identifier)
TEST(ParserA607, CaseComplexExpr) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    case(a + b)\n"
                 "      0: y = 1;\n"
                 "      1: y = 2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}
