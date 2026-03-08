#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, BeginKeywords1800_2005_LogicIsKeyword) {

  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module t;\n"
                              "  logic [7:0] data;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2005_InterfaceIsKeyword) {

  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "interface if1;\n"
                              "endinterface\n"
                              "`end_keywords\n"));
}

}
