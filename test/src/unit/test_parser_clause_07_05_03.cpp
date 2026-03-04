// §7.5.3: Delete()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
namespace {

TEST(ParserSection7c, DynamicArrayDelete) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    dyn.delete();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
TEST(ParserSection7, DynamicArrayDeleteMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial dyn.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

}  // namespace
