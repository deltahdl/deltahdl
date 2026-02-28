// §5.7.1: Integer literal constants

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § octal_digit — 0 through 7
TEST(ParserA87, OctalDigitAll) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'o01234567; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 01234567u);
}

}  // namespace
