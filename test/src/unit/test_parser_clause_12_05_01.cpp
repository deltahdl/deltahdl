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

// ---------------------------------------------------------------------------
// case_keyword ::= case | casez | casex
// ---------------------------------------------------------------------------
// §12.5.1: casez keyword
TEST(ParserA607, CasezKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casez(sel) 3'b1??: x = 1; default: x = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

// §12.5.1: casex keyword
TEST(ParserA607, CasexKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casex(sel) 3'b1??: x = 1; default: x = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
}

// Casez inside always_ff.
TEST(ParserSection12, CasezInsideAlwaysFF) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  logic [1:0] sel;\n"
              "  logic [3:0] q;\n"
              "  always_ff @(posedge clk) begin\n"
              "    casez (sel)\n"
              "      2'b1?: q <= 4'd1;\n"
              "      2'b01: q <= 4'd2;\n"
              "      default: q <= 4'd0;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 20. casex inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CasexStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] sel, q, a, b;\n"
      "  always_latch\n"
      "    casex (sel)\n"
      "      4'b1xxx: q <= a;\n"
      "      4'b01xx: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_kind, TokenKind::kKwCasex);
}

// ---------------------------------------------------------------------------
// 21. casez inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CasezStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] sel, q, a, b;\n"
      "  always_latch\n"
      "    casez (sel)\n"
      "      4'b1???: q <= a;\n"
      "      4'b01??: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_kind, TokenKind::kKwCasez);
}

// =============================================================================
// LRM section 12.5.1 -- casex / casez
// =============================================================================
TEST(ParserSection12, CasexStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casex (sel)\n"
      "      2'b1?: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 2u);
}

TEST(ParserSection12, CasezStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casez (sel)\n"
      "      2'b1?: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 2u);
}

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
