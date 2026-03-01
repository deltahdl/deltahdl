// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9g Parse(const std::string& src) {
  ParseResult9g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysComb(ParseResult9g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) return item;
  }
  return nullptr;
}

static Stmt* FirstAlwaysCombStmt(ParseResult9g& r) {
  auto* item = FirstAlwaysComb(r);
  if (!item || !item->body) return nullptr;
  if (item->body->kind == StmtKind::kBlock) {
    return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
  }
  return item->body;
}

namespace {

// =============================================================================
// LRM section 9.2.2 -- Always_comb procedure
//
// The always_comb procedure is a combinational logic process with an
// implicit sensitivity list. It executes once at time zero and then
// re-executes whenever any of its input signals change. No explicit
// sensitivity list is permitted.
// =============================================================================
// ---------------------------------------------------------------------------
// 1. Simple blocking assignment in always_comb
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_SimpleBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 2. always_comb with begin-end block containing multiple assignments
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_BeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 3. always_comb with if-else statement
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_IfElse) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      y = a;\n"
      "    else\n"
      "      y = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 4. always_comb with case statement
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  ASSERT_EQ(stmt->case_items.size(), 4u);
  EXPECT_TRUE(stmt->case_items[3].is_default);
}

// ---------------------------------------------------------------------------
// 5. always_comb with casex statement
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_CasexStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] opcode;\n"
      "  logic [7:0] result;\n"
      "  always_comb begin\n"
      "    casex (opcode)\n"
      "      4'b1xxx: result = 8'hFF;\n"
      "      4'b01xx: result = 8'h0F;\n"
      "      default: result = 8'h00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 6. always_comb with casez statement
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_CasezStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    casez (req)\n"
      "      4'b???1: grant = 2'b00;\n"
      "      4'b??10: grant = 2'b01;\n"
      "      4'b?100: grant = 2'b10;\n"
      "      4'b1000: grant = 2'b11;\n"
      "      default: grant = 2'b00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

}  // namespace
