#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Shared syntactic form: dotted names parse as kMemberAccess ---

TEST(DottedNameParsing, MemberAccessExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = obj.field;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(DottedNameParsing, MemberAssignment) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.a = 10;\n"
      "    p.b = 20;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 0);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(DottedNameParsing, StructMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  struct { int x; int y; } s;\n"
      "  initial s.x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(DottedNameParsing, MultiLevelDottedNameTreeStructure) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a.b.c;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->lhs->text, "a");
  ASSERT_NE(rhs->lhs->rhs, nullptr);
  EXPECT_EQ(rhs->lhs->rhs->text, "b");
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "c");
}

TEST(DottedNameParsing, DottedNameInContinuousAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire [7:0] y;\n"
              "  assign y = a.b;\n"
              "endmodule\n"));
}

TEST(DottedNameParsing, DottedNameAsFunctionArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function int f(int x);\n"
              "    return x;\n"
              "  endfunction\n"
              "  initial x = f(obj.field);\n"
              "endmodule\n"));
}

TEST(DottedNameParsing, DottedNameInConditionalExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = sel ? a.b : c.d;\n"
              "endmodule\n"));
}

// Struct and hierarchical dotted names parse identically.

TEST(DottedNameParsing, StructSelectAndHierarchicalSameSyntacticForm) {
  auto r1 = Parse(
      "module t;\n"
      "  typedef struct { int x; } s_t;\n"
      "  s_t s;\n"
      "  initial x = s.x;\n"
      "endmodule\n");
  auto r2 = Parse(
      "module t;\n"
      "  initial x = inst.sig;\n"
      "endmodule\n");
  auto* rhs1 = FirstInitialRHS(r1);
  auto* rhs2 = FirstInitialRHS(r2);
  ASSERT_NE(rhs1, nullptr);
  ASSERT_NE(rhs2, nullptr);
  EXPECT_EQ(rhs1->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(rhs2->kind, ExprKind::kMemberAccess);
}

TEST(DottedNameParsing, UnionMemberAccessDottedName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  union { int a; logic [31:0] b; } u;\n"
              "  initial x = u.a;\n"
              "endmodule\n"));
}

TEST(DottedNameParsing, ClassMemberAccessDottedName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  class C;\n"
              "    int val;\n"
              "  endclass\n"
              "  C obj;\n"
              "  initial x = obj.val;\n"
              "endmodule\n"));
}

TEST(DottedNameParsing, FourLevelDottedName) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a.b.c.d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "d");
}

TEST(DottedNameParsing, DottedNameOnBothSidesOfAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial a.x = b.y;\n"
              "endmodule\n"));
}

}  // namespace
