#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection4, Sec4_6_UniqueCaseOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      2'b10: y = 2;\n"
      "      2'b11: y = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection4, Sec4_6_Unique0CaseAtMostOneMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ParserSection4, Sec4_6_PriorityCaseFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserSection9, Sec9_2_2_UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "      2'b11: y = 4'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

TEST(ParserSection12, UniqueCasezQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casez (sel)\n"
      "      2'b1?: x = 1;\n"
      "      2'b01: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection9, Sec9_2_2_PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    priority case (1'b1)\n"
      "      req[0]: grant = 2'd0;\n"
      "      req[1]: grant = 2'd1;\n"
      "      req[2]: grant = 2'd2;\n"
      "      req[3]: grant = 2'd3;\n"
      "      default: grant = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

TEST(ParserSection12, PriorityCasex) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority casex (sel)\n"
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
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserSection9, Sec9_4_2_3_AtStarUniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg out;\n"
      "  always @* begin\n"
      "    unique case (sel)\n"
      "      2'b00: out = 0;\n"
      "      2'b01: out = 1;\n"
      "      default: out = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  auto* case_stmt = GetAlwaysStarCaseStmt(r);
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection4, Sec4_6_PriorityCaseWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (opcode)\n"
      "      4'h0: result = a + b;\n"
      "      4'h1: result = a - b;\n"
      "      4'h2: result = a & b;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

TEST(ParserSection4, Sec4_6_UniqueCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (state)\n"
      "      IDLE: x = 0;\n"
      "      RUN: x = 1;\n"
      "      DONE: x = 2;\n"
      "      ERR: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_EQ(stmt->case_items.size(), 4u);
}

TEST(ParserSection9, Sec9_2_2_Unique0Case) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

TEST(ParserSection12, UniqueCase) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection12, PriorityCase) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      0: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserA607, UniqueCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

TEST(ParserSection9, Sec9_2_3_UniqueCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b, c;\n"
      "  always_latch\n"
      "    unique case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      2'b10: q <= c;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique);
}

TEST(ParserSection12, UniqueCaseInsideAlwaysComb) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [1:0] sel;\n"
              "  logic [7:0] out;\n"
              "  always_comb begin\n"
              "    unique case (sel)\n"
              "      2'd0: out = 8'hAA;\n"
              "      2'd1: out = 8'hBB;\n"
              "      2'd2: out = 8'hCC;\n"
              "      2'd3: out = 8'hDD;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA607, Unique0CaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(ParserSection9, Sec9_2_3_PriorityCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    priority case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kPriority);
}

TEST(ParserA607, PriorityCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case(x)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserA607, PriorityCasezParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority casez(a)\n"
      "      3'b00?: y = 1;\n"
      "      3'b0??: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(ParserSection12, Unique0CaseWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(ParserSection9, Sec9_2_3_Unique0CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    unique0 case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique0);
}

TEST(ParserSection12, UniqueCasexQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casex (sel)\n"
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
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

}  // namespace
