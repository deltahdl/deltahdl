#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsOrEmpty_Semicolon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}
