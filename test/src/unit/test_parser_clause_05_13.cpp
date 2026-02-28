// §5.13: Built-in methods

#include "fixture_parser.h"

using namespace delta;

// --- §5.13 Built-in methods ---
struct ParseResult513 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static Stmt* FirstInitialStmt(ParseResult513& r) {
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

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserCh513, BuiltInMethodCall_ChainedAccess) {
  // Chained member access: obj.arr.size() parses as a call.
  auto r = Parse(
      "module t;\n"
      "  initial x = obj.arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// From test_parser_clause_05b.cpp
TEST(ParserCh513, BuiltInMethod_NoParens) {
  // When a method has no arguments the parentheses are optional.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.size;\n"
              "endmodule"));
}

}  // namespace
