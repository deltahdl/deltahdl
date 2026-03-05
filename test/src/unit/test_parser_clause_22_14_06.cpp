#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §22.14.6 — IEEE Std 1800-2005 keywords

TEST(ParserSection22, BeginKeywords1800_2005_LogicIsKeyword) {
  // "logic" is a keyword in 1800-2005; using it as a data type should parse.
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module t;\n"
                              "  logic [7:0] data;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2005_InterfaceIsKeyword) {
  // "interface" is a keyword in 1800-2005; it should parse as a declaration.
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "interface if1;\n"
                              "endinterface\n"
                              "`end_keywords\n"));
}

}  // namespace
