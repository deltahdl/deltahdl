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

Stmt *FirstInitialStmt(ParseResult &r) {
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
// A.8 -- Expressions
// =============================================================================

TEST(ParserAnnexA, A8TernaryExpr) {
  auto r = Parse("module m; initial x = (a > b) ? a : b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(ParserAnnexA, A8Concatenation) {
  auto r = Parse("module m; initial x = {a, b, c}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(ParserAnnexA, A8Replication) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(ParserAnnexA, A8SystemFunctionCall) {
  auto r = Parse("module m; initial begin $display(\"v=%0d\", x); $finish; end "
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A8MemberAccess) {
  auto r = Parse("module m; initial x = s.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserAnnexA, A8BitAndPartSelect) {
  auto r = Parse("module m;\n"
                 "  initial begin x = data[3]; y = data[7:4]; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A8FunctionCallExpr) {
  auto r = Parse("module m; initial x = func(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserAnnexA, A8IntegerLiterals) {
  auto r = Parse("module m;\n"
                 "  initial begin a = 42; b = 8'hFF; c = 4'b1010; end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
