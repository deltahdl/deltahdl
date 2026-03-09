#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_13_MethodCallWithParens) {
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

TEST(ParserClause05, Cl5_13_MethodCallNoParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.size;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_ChainedAccess) {
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

TEST(ParserClause05, Cl5_13_MethodWithArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] q [$];\n"
              "  initial q.push_back(8'hAA);\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_MethodInExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:3];\n"
              "  int r;\n"
              "  initial r = arr.size() + 1;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_MutatingMethodStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:2];\n"
              "  initial arr.reverse();\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_MutatingMethodStatementNoParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:2];\n"
              "  initial arr.reverse;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_QueueDelete) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q [$];\n"
              "  initial q.delete();\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_QueuePopFront) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q [$];\n"
              "  int v;\n"
              "  initial v = q.pop_front();\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_ReductionSum) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:2];\n"
              "  int total;\n"
              "  initial total = arr.sum();\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_13_DynArraySize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int dyn [];\n"
              "  int s;\n"
              "  initial s = dyn.size();\n"
              "endmodule\n"));
}

}  // namespace
