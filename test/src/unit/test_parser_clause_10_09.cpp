// §10.9: Assignment patterns

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 20. Struct with type-prefixed assignment pattern T'{...}.
TEST(ParserSection7, Sec7_2_2_TypePrefixedPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'{100, 200};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
