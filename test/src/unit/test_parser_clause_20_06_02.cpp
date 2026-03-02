// §20.6.2: Expression size system function

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// system_tf_call with expression argument: $bits(variable)
TEST(ParserA82, SystemTfCallBitsExprArg) {
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

}  // namespace
