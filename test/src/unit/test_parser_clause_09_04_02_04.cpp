// §9.4.2.4: Sequence events

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection9c, SequenceEventParenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s1;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    @(s1) $display(\"matched\");\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
