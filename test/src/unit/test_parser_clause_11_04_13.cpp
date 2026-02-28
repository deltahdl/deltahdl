// §11.4.13: for an explanation of range list syntax.

#include "fixture_parser.h"

using namespace delta;

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

TEST(ParserSection11, InsideBasicListCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 3u);
}

TEST(ParserSection11, InsideBasicListLhs) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection11, InsideWithRange) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
}

TEST(ParserSection11, InsideWithRangeElements) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->elements.size(), 2u);
}

TEST(ParserSection11, InsideInAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire r;\n"
      "  assign r = a inside {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
