// §11.2.2: Aggregate expressions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 18. Struct comparison with another struct.
TEST(ParserSection7, Sec7_2_2_StructComparison) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial eq = (x == y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kEqEq);
}

}  // namespace
