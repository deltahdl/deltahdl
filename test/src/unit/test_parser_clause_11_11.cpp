// §11.11: Minimum, typical, and maximum delay expressions

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// delay2: mintypmax expression in parenthesized form.
TEST(ParserA223, Delay2MintypMaxSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(1:2:3) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->kind, ExprKind::kMinTypMax);
}

// =============================================================================
// A.8.3 Expressions — constant_mintypmax_expression
// =============================================================================
// § constant_mintypmax_expression ::= constant_expression :
// constant_expression : constant_expression
TEST(ParserA83, ConstantMinTypMaxInSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tpd = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.3 Expressions — mintypmax_expression
// =============================================================================
// § mintypmax_expression ::= expression : expression : expression
TEST(ParserA83, MinTypMaxInDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #(1:2:3) y = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § mintypmax_expression ::= expression (single form)
TEST(ParserA83, MinTypMaxSingleExpr) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #5 y = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_primary — parenthesized constant_mintypmax_expression
TEST(ParserA84, ConstantPrimaryParenthesized) {
  auto r = Parse("module m; parameter int P = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kBinary);
}

// =========================================================================
// Section 11.7 -- Minimum, typical, and maximum delay expressions
// =========================================================================
TEST(ParserSection11, MinTypMaxInGateDelay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire a, b, c;\n"
              "  and #(2:3:4) g1(c, a, b);\n"
              "endmodule\n"));
}

}  // namespace
