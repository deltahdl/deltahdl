#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh501, Sec5_1_KeywordsAreReserved) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  logic l;\n"
              "  assign w = 0;\n"
              "  initial begin\n"
              "    if (l) w = 1;\n"
              "    else w = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserCh50602, Keyword_AllLowercase) {
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

}  // namespace
