#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ExpressionParsing, ConstantMinTypMaxInSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tpd = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, MinTypMaxSingleExpr) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #5 y = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, MinTypMaxInSpecparam) {
  EXPECT_TRUE(
      ParseOk("module t(input a, output b);\n"
              "  specify\n"
              "    specparam tRise = 1:2:3;\n"
              "  endspecify\n"
              "endmodule\n"));
}

}  // namespace
