// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// § primary — cast
TEST(ParserA84, PrimaryCast) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = int'(3.14);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

}  // namespace
