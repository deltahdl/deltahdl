

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BlockingAssignParsing, ConcatenationLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin {a, b} = {c, d}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(BlockingAssignParsing, BitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin mem[3] = 8'hFF; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(BlockingAssignParsing, PartSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin data[7:0] = 8'hAB; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(BlockingAssignParsing, BinaryExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = a + b * c; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(BlockingAssignParsing, FunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = func(a, b); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(BlockingAssignParsing, SimpleBlocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "a");
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->text, "b");
}

TEST(BlockingAssignParsing, InBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    y = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->text, "x");
  EXPECT_EQ(s1->lhs->text, "y");
}

TEST(BlockingAssignParsing, MultipleSequential) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    c = 0;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto [s0, s1, s2, s3] = Get4InitialStmts(r);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s3->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
  EXPECT_EQ(s3->lhs->text, "a");
}

TEST(BlockingAssignParsing, ArrayElementLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr[2] = 8'hAB;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}


TEST(BlockingAssignParsing, NestedStructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.inner.field = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(BlockingAssignParsing, ComplexLhsRhsCombinations) {
  auto r = Parse(
      "module m;\n"
      "  reg [15:0] data;\n"
      "  reg [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    data[7:0] = arr[0] + arr[1];\n"
      "    data[15:8] = arr[2] & arr[3];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(s1->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(s0->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(s1->rhs->kind, ExprKind::kBinary);
}

TEST(BlockingAssignParsing, StructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.field = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

}  // namespace
