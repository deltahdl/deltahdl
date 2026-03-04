// §7.9.1: Num() and size()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// §7.9: Associative array methods
// =========================================================================
TEST(ParserSection7, AssocArrayNumMethod) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial x = aa.num();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

}  // namespace
