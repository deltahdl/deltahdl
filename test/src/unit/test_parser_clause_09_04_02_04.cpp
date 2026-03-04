// §9.4.2.4: Sequence events

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
// =============================================================================
// §9.4.2.4 -- Sequence events
// =============================================================================
TEST(ParserSection9b, SequenceEventInEventControl) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial @(abc) $display(\"match\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
