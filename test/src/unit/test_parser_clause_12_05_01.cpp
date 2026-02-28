// §12.5.1: Case statement with do-not-cares

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

// =============================================================================
// LRM section 12.5.1 -- casex / casez (additional cases)
// =============================================================================
// casez with wildcard question-mark pattern.
TEST(ParserSection12, CasezWithQuestionMark) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casez (ir)\n"
      "      8'b1???????: x = 1;\n"
      "      8'b01??????: x = 2;\n"
      "      8'b00010???: x = 3;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// casex with multiple case items and expressions.
TEST(ParserSection12, CasexMultipleItemsWithExpressions) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casex (data)\n"
      "      8'b001100xx: x = 1;\n"
      "      8'b1100xx00: x = 2;\n"
      "      8'b00xx0011: x = 3;\n"
      "      8'bxx010100: x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

}  // namespace
