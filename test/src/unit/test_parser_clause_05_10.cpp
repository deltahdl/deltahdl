// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_10_EmptyAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial x = '{};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 0u);
}

}  // namespace
