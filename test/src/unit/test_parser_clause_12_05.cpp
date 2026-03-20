#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessParsing, BlockWithCaseStatement) {
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

TEST(AssignmentParsing, CaseDecoderPattern) {
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

TEST(ProceduralStatementParsing, CaseInsideForLoop) {
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

TEST(ProcessParsing, CaseStatement) {
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

TEST(AssignmentParsing, InCaseItems) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] out;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: out = 8'h00;\n"
      "      2'b01: out = 8'h11;\n"
      "      2'b10: out = 8'h22;\n"
      "      default: out = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kBlockingAssign);
}

}  // namespace
