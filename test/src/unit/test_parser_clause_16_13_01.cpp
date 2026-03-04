#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection16, MulticlockSequenceDeclTwo) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_multi;\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
