#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SignedExprPreprocessor, SignedThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = $signed(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
}

TEST(SignedExprPreprocessor, UnsignedThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic signed [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = $unsigned(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$unsigned");
}

}  // namespace
