#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssignmentParsing, OperatorAssignPlusEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AssignmentParsing, OperatorAssignMinusEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a -= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignStarEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a *= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignSlashEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a /= 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignPercentEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a %= 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignAmpEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a &= 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignPipeEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a |= 8'h01;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignCaretEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignLtLtEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a <<= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignGtGtEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a >>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignLtLtLtEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a <<<= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssignmentParsing, OperatorAssignGtGtGtEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
