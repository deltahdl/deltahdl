#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceMatchItem_SubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, $display(\"match\")) |-> c);\n"
              "endmodule\n"));
}

}
