#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §11.2: "Any legal operand, such as a net bit-select, without any operator
// is considered an expression."  Each test verifies that one operand kind
// from the §11.2 operand list parses as a standalone expression.

TEST(OperandAsExpression, IntegerLiteral) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(OperandAsExpression, RealLiteral) {
  auto r = Parse(
      "module m;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(OperandAsExpression, StringLiteral) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(OperandAsExpression, VariableIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
}

TEST(OperandAsExpression, BitSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic b;\n"
      "  initial b = a[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperandAsExpression, PartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial b = a[3:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(OperandAsExpression, IndexedPartSelectUp) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial b = a[0+:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(OperandAsExpression, IndexedPartSelectDown) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial b = a[7-:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

TEST(OperandAsExpression, StructureMember) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "  s_t s;\n"
      "  int x;\n"
      "  initial x = s.a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(OperandAsExpression, PackedStructBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; } s_t;\n"
      "  s_t s;\n"
      "  logic x;\n"
      "  initial x = s.a[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kMemberAccess);
}

TEST(OperandAsExpression, UnionMember) {
  auto r = Parse(
      "module m;\n"
      "  typedef union { int a; } u_t;\n"
      "  u_t u;\n"
      "  int x;\n"
      "  initial x = u.a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(OperandAsExpression, PackedUnionBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef union packed { logic [7:0] a; } u_t;\n"
      "  u_t u;\n"
      "  logic x;\n"
      "  initial x = u.a[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kMemberAccess);
}

TEST(OperandAsExpression, ArrayElementSelect) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  int x;\n"
      "  initial x = arr[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(OperandAsExpression, FunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int foo();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(OperandAsExpression, SystemFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial x = $clog2(8);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
}

}  // namespace
