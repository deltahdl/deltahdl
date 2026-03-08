#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, SequencePortItem_LocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceLvarPortDirection_Input) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input int x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceLvarPortDirection_Output) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output int x);\n"
              "    (1, x = a) ##1 (1, x = b);\n"
              "  endsequence\n"
              "endmodule\n"));
}

}
