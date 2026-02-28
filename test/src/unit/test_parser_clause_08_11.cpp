// §8.11: This

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — this
TEST(ParserA84, PrimaryThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
