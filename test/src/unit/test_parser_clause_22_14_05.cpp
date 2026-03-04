#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1364_2005) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}
