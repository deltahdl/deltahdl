#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection9, Sec9_3_1_BlockWithCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (mode)\n"
      "      0: a = 1;\n"
      "      1: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_GE(stmt->case_items.size(), 3u);
}

TEST(ParserSection10, Sec10_4_2_CaseDecoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: q <= 8'h00;\n"
      "      2'b01: q <= 8'h01;\n"
      "      2'b10: q <= 8'h10;\n"
      "      default: q <= 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserSection12, CaseMultipleExprsPerItem) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0, 1: x = 1;\n"
      "      2, 3: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 3u);

  EXPECT_EQ(stmt->case_items[0].patterns.size(), 2u);
}

TEST(ParserSection12, CaseWithOnlyDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 1u);
  EXPECT_TRUE(stmt->case_items[0].is_default);
}

TEST(ParserA607, CaseStmtItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(ParserA607, CaseMultipleItemExprs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(sel)\n"
      "      0, 1: x = 8'd10;\n"
      "      2, 3, 4: x = 8'd20;\n"
      "      default: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 2u);
  EXPECT_EQ(stmt->case_items[1].patterns.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(ParserA607, CaseDefaultNoColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(ParserA607, CaseNoDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; 1: y = 2; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_FALSE(stmt->case_items[1].is_default);
}

TEST(ParserA607, CaseItemWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x)\n"
      "      0: begin y = 1; z = 2; end\n"
      "      default: begin y = 0; z = 0; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlock);
}

TEST(ParserSection12, PlainCaseHasNoQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

TEST(ParserSection12, CaseInsideForLoop) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    for (int i = 0; i < 4; i = i + 1) begin\n"
              "      case (mode)\n"
              "        0: data[i] = 0;\n"
              "        1: data[i] = i;\n"
              "        default: data[i] = 8'hFF;\n"
              "      endcase\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection12, PlainCaseIsNotInside) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (val)\n"
      "      0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_FALSE(stmt->case_inside);
}

TEST(ParserA604, StmtItemCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      1: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(ParserA607, NestedCaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(a)\n"
      "      0: case(b)\n"
      "           0: x = 1;\n"
      "           1: x = 2;\n"
      "         endcase\n"
      "      1: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kCase);
}

TEST(ParserA607, CaseStmtParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
}

TEST(ParserA607, CaseItemNullBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x)\n"
      "      0: ;\n"
      "      1: y = 1;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

TEST(ParserA607, CaseComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(a + b)\n"
      "      0: y = 1;\n"
      "      1: y = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
}

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

}  // namespace
