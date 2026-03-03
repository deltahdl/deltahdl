// Non-LRM tests

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

TEST(ParserSection7, StructMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  struct { int x; int y; } s;\n"
      "  initial s.x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7c, DynamicArrayNewConstruct) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial dyn = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, DynamicArraySize) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    sz = dyn.size();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, DynamicArrayDelete) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    dyn.delete();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 7.7 -- Queues
// =============================================================================
TEST(ParserSection7c, QueueDecl) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueueWithMaxSize) {
  auto r = Parse(
      "module m;\n"
      "  int q[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
