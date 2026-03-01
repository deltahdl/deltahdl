// §7.10.2.1: Size()

#include "fixture_parser.h"

using namespace delta;

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static Stmt* FirstInitialStmt(ParseResult7b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// --- Test helpers ---
struct ParseResult7c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7c Parse(const std::string& src) {
  ParseResult7c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection7, QueueSizeMethod) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial x = q.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueueMethodSize) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial y = q.size;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

}  // namespace
