#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, RealToIntAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    r = 35.7;\n"
              "    i = r;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, IntToRealAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    i = 42;\n"
              "    r = i;\n"
              "  end\n"
              "endmodule\n"));
}

}
