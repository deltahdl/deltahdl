#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NumberParsing, UnaryPlusBeforeLiteral) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  logic [7:0] x;\n"
               "  initial x = +42;\n"
               "endmodule\n"));
}

TEST(NumberParsing, UnaryPlusBeforeSizedLiteral) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  logic [7:0] x;\n"
               "  initial x = +8'hFF;\n"
               "endmodule\n"));
}

}  // namespace
