#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// §20.6.2 BNF: the size_function alternative that takes a data_type as its
// sole argument shall be accepted by the parser (NC4, data_type form).
TEST(SubroutineCallExprParsing, SystemTfCallBitsDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  parameter int W = $bits(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §20.6.2 BNF: the data_type argument form also admits a ranged built-in type,
// e.g. $bits(logic [7:0]) — a distinct syntactic argument from a bare type
// keyword. The parser shall accept it.
TEST(SubroutineCallExprParsing, SystemTfCallBitsRangedDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  parameter int W = $bits(logic [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
