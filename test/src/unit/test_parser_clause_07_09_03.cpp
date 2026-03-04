// §7.9.3: Exists()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection7, AssocArrayExistsMethod) {
  auto r = Parse("module t;\n"
                 "  int aa[string];\n"
                 "  initial x = aa.exists(\"key\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

} // namespace
