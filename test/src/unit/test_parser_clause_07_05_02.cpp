#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DynamicArraySizeParsing, DynamicArraySize) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    sz = dyn.size();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DynamicArraySizeParsing, DynamicArraySizeMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial x = dyn.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

}  // namespace
