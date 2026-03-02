// §18.11: Inline random variable control

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA82, RandomizeCallWithVarList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(x, y); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
