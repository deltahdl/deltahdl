#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OperatorAndExpressionParsing, AllBinaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a ** b;\n"
              "    x = a == b;\n"
              "    x = a != b;\n"
              "    x = a === b;\n"
              "    x = a !== b;\n"
              "    x = a ==? b;\n"
              "    x = a !=? b;\n"
              "    x = a < b;\n"
              "    x = a <= b;\n"
              "    x = a > b;\n"
              "    x = a >= b;\n"
              "    x = a && b;\n"
              "    x = a || b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a ~^ b;\n"
              "    x = a ^~ b;\n"
              "    x = a << b;\n"
              "    x = a >> b;\n"
              "    x = a <<< b;\n"
              "    x = a >>> b;\n"
              "    x = a -> b;\n"
              "    x = a <-> b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, AllUnaryOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = +a;\n"
              "    x = -a;\n"
              "    x = ~a;\n"
              "    x = !a;\n"
              "    x = &a;\n"
              "    x = |a;\n"
              "    x = ^a;\n"
              "    x = ~&a;\n"
              "    x = ~|a;\n"
              "    x = ~^a;\n"
              "    x = ^~a;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, AllAssignmentOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = 0;\n"
              "    x += 1;\n"
              "    x -= 1;\n"
              "    x *= 1;\n"
              "    x /= 1;\n"
              "    x %= 1;\n"
              "    x &= 1;\n"
              "    x |= 1;\n"
              "    x ^= 1;\n"
              "    x <<= 1;\n"
              "    x >>= 1;\n"
              "    x <<<= 1;\n"
              "    x >>>= 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, ConditionalExpressionParses) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ? b : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(OperatorAndExpressionParsing, IncDecOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    ++x;\n"
              "    --x;\n"
              "    x++;\n"
              "    x--;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, StreamOperatorsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    x = {>> {a, b}};\n"
              "    x = {<< {a, b}};\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
