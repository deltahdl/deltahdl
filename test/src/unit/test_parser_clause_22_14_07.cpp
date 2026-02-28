// §22.14.7: IEEE Std 1800-2009 keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2009) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2009\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}  // namespace
