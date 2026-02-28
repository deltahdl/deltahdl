// §16.11: Calling subroutines on match of a sequence

#include "fixture_parser.h"

using namespace delta;


namespace {

// sequence_match_item ::= subroutine_call
TEST(ParserA210, SequenceMatchItem_SubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, $display(\"match\")) |-> c);\n"
              "endmodule\n"));
}

}  // namespace
