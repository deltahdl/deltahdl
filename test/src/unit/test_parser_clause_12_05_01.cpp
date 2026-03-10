#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

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
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

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
  auto* body = FirstAlwaysCombStmt(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

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
  auto* body = FirstAlwaysCombStmt(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

}  // namespace
