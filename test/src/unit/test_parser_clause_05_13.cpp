#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BuiltinMethodParsing, MethodCallWithParens) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:3];\n"
      "  int s;\n"
      "  initial s = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(BuiltinMethodParsing, MethodCallNoParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.size;\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, ChainedAccess) {
  auto r = Parse(
      "module m;\n"
      "  initial x = obj.arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(BuiltinMethodParsing, MethodWithArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] q [$];\n"
              "  initial q.push_back(8'hAA);\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, MethodInExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:3];\n"
              "  int r;\n"
              "  initial r = arr.size() + 1;\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, QueueDelete) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q [$];\n"
              "  initial q.delete();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, QueuePopFront) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q [$];\n"
              "  int v;\n"
              "  initial v = q.pop_front();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, DynArraySize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int dyn [];\n"
              "  int s;\n"
              "  initial s = dyn.size();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, StringMethodParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  string s;\n"
              "  int n;\n"
              "  initial n = s.len();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, AssocArrayMethodParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int assoc [string];\n"
              "  int n;\n"
              "  initial n = assoc.num();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, EnumMethodParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {A, B, C} abc_e;\n"
              "  abc_e e;\n"
              "  int n;\n"
              "  initial n = e.num();\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, MethodCallWithMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q [$];\n"
              "  initial q.insert(0, 42);\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, MethodCallCalleeIsMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:3];\n"
      "  int s;\n"
      "  initial s = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kCall);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

TEST(BuiltinMethodParsing, MethodWithDefaultArgNoParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum {A, B, C} abc_e;\n"
              "  abc_e e;\n"
              "  abc_e n;\n"
              "  initial n = e.next;\n"
              "endmodule\n"));
}

TEST(BuiltinMethodParsing, MethodNoParensIsMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2];\n"
      "  int s;\n"
      "  initial s = arr.size;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(BuiltinMethodParsing, MethodNoParensInBinaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:3];\n"
              "  int r;\n"
              "  initial r = arr.size + 1;\n"
              "endmodule\n"));
}

}  // namespace
