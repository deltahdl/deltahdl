#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1364_2001) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}
