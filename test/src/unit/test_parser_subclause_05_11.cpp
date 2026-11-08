#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(ArrayLiteralParsing, ArrayLiteralExprKind) {
  auto r = Parse(
      "module m;\n"
      "  int n [1:3];\n"
      "  initial n = '{0, 1, 2};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ArrayLiteralParsing, NestedBracesFollowDimensions) {
  auto r = Parse(
      "module m;\n"
      "  int n [1:2][1:3];\n"
      "  initial n = '{'{0, 1, 2}, '{3, 4, 5}};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kAssignmentPattern);
}

TEST(ArrayLiteralParsing, ReplicationParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n [1:3];\n"
              "  initial n = '{3{4}};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, NestedReplicationParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n [1:2][1:6];\n"
              "  initial n = '{2{'{3{4, 5}}}};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, TypePrefixedArrayLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  triple b = triple'{0, 1, 2};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, IndexAndDefaultKeyParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  triple b = '{1:1, default:0};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, TypePrefixedLiteralAsExpressionOperand) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  initial $display(triple'{0, 1, 2});\n"
              "endmodule\n"));
}

}  // namespace
