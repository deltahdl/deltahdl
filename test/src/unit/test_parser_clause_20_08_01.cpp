#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemFunction_InExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
}
TEST(ParserSection11, ConstExprSystemFuncInParam) {
  auto r = Parse(
      "module t;\n"
      "  parameter N = 16;\n"
      "  parameter BITS = $clog2(N);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, SystemTfCallAsExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$clog2");
  EXPECT_EQ(stmt->rhs->args.size(), 1u);
}

TEST(ParserA84, PrimarySystemCall) {
  auto r = Parse("module m; initial x = $clog2(16); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
}

}
