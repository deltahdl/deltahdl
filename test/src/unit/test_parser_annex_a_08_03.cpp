#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA83, ExprOperatorAssignment) {
  auto r = Parse("module m; initial x = (y += 1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
