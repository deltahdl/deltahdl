// §22.14.9: IEEE Std 1800-2017 and IEEE Std 1800-2023 keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2017) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsWithModuleContent) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "  logic [7:0] data;\n"
              "  initial data = 8'hFF;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

}  // namespace
