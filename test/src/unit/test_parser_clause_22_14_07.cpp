#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2009) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2009\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}
