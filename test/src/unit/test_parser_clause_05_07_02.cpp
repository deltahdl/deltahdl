#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.7.2: Real literal constants
// =========================================================================

struct ParseResult50702 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult50702 Parse(const std::string &src) {
  ParseResult50702 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt *FirstInitialStmt(ParseResult50702 &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

TEST(ParserCh50702, RealLiteral_DecimalNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 14.72;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 14.72);
}

TEST(ParserCh50702, RealLiteral_ScientificNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1.30e-2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 0.013);
}

TEST(ParserCh50702, RealLiteral_ExponentOnly) {
  // 39e8 is a valid real constant (exponent notation without decimal point).
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  initial r = 39e8;\n"
              "endmodule"));
}
