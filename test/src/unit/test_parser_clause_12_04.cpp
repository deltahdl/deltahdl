// §12.4: Conditional if–else statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult12b& r) {
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

TEST(ParserSection12, NestedIfElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Else associates with the inner if
  EXPECT_EQ(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

TEST(ParserSection12, IfWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

}  // namespace
