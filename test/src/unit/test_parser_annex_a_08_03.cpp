// Annex A.8.3: Expressions

#include "fixture_parser.h"

using namespace delta;

namespace {

// § expression ::= ( operator_assignment )
TEST(ParserA83, ExprOperatorAssignment) {
  auto r = Parse("module m; initial x = (y += 1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
