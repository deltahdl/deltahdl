// §5.9: String literals

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary_literal — string_literal
TEST(ParserA84, PrimaryLiteralStringLiteral) {
  auto r = Parse("module m; initial x = \"world\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

}  // namespace
