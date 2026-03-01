// §22.14.8: IEEE Std 1800-2012 keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2012) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2012\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}  // namespace
