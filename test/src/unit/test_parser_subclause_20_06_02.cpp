#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprParsing, SystemTfCallBitsExprArg) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  initial x = $bits(v);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$bits");
}

TEST(PrimaryParsing, ConstantPrimaryTypeReference) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  parameter int W = $bits(x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, SystemTfCallBitsDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  parameter int W = $bits(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, SystemTfCallBitsRangedDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  parameter int W = $bits(logic [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
