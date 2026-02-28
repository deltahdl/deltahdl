// §22.14.4: IEEE Std 1364-2001-noconfig keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1364_2001_noconfig) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2001-noconfig\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}  // namespace
