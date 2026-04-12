#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignParsing, ProceduralAssignKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, ProceduralAssignLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
}

TEST(ProceduralAssignDeassignParsing, ProceduralDeassignKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  EXPECT_EQ(stmt->rhs, nullptr);
}

TEST(ProceduralAssignDeassignParsing, ProceduralDeassignLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
}
TEST(ProceduralAssignDeassignParsing, ProceduralAssignThenDeassign) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 1;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kDeassign);
}

TEST(ProceduralAssignDeassignParsing, ProceduralAssignConcatLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ProceduralAssignDeassignParsing, ProceduralDeassignConcatLhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ProceduralAssignDeassignParsing, ProceduralAssignExpressionRhs) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    assign c = a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(ProceduralAssignDeassignParsing, DFlipFlopClearPresetPattern) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk(
          "module dff(output reg q, input d, clear, preset, clock);\n"
          "  always @(clear or preset)\n"
          "    if (!clear)\n"
          "      assign q = 0;\n"
          "    else if (!preset)\n"
          "      assign q = 1;\n"
          "    else\n"
          "      deassign q;\n"
          "  always @(posedge clock)\n"
          "    q <= d;\n"
          "endmodule\n"));
}

}  // namespace
