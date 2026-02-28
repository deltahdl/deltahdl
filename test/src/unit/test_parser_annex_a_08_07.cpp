// Annex A.8.7: Numbers

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § x_digit — X
TEST(ParserA87, XDigitUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hX; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
