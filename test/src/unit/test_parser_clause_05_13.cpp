#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- §5.13 Built-in methods ---

struct ParseResult513 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult513 Parse(const std::string &src) {
  ParseResult513 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult513 &r) {
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

// From test_parser_clause_05.cpp

TEST(ParserCh513, BuiltInMethodCall_Parse) {
  auto r = Parse("module t;\n"
                 "  initial x = arr.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserCh513, BuiltInMethodCall_Callee) {
  // The callee_expr should be the full member-access expression.
  auto r = Parse("module t;\n"
                 "  initial x = arr.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserCh513, BuiltInMethodCall_ChainedAccess) {
  // Chained member access: obj.arr.size() parses as a call.
  auto r = Parse("module t;\n"
                 "  initial x = obj.arr.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// From test_parser_clause_05b.cpp

TEST(ParserCh513, BuiltInMethod_NoParens) {
  // When a method has no arguments the parentheses are optional.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial x = q.size;\n"
                      "endmodule"));
}

TEST(ParserCh513, BuiltInMethod_ChainedAccess) {
  // Chained member accesses: a.b.c().
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial x = obj.sub.method();\n"
                      "endmodule"));
}

TEST(ParserCh513, BuiltInMethod_WithArgs) {
  // Built-in method with arguments: arr.find with (item > 3).
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial q.sort();\n"
                      "endmodule"));
}

TEST(ParserCh513, BuiltInMethod_Delete) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial q.delete();\n"
                      "endmodule"));
}

TEST(ParserCh513, BuiltInMethod_PushBack) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial q.push_back(42);\n"
                      "endmodule"));
}
