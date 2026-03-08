#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, AssignInExprParenthesized) {
  auto r = Parse(
      "module t;\n"
      "  initial if ((a = b)) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial b = (a += 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
