#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================

struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult50603 Parse(const std::string &src) {
  ParseResult50603 result;
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

static Stmt *FirstInitialStmt(ParseResult50603 &r) {
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

TEST(ParserCh50603, SystemTask_Display) {
  // $display is a system task call (Section 5.6.3, Section 21.2).
  auto r = Parse("module m;\n"
                 "  initial $display(\"hello\");\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserCh50603, SystemTask_FinishNoArgs) {
  // $finish with no arguments and no parentheses.
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

TEST(ParserCh50603, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  parameter W = $clog2(256);\n"
                      "endmodule"));
}
