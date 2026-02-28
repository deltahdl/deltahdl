// §12.7.6: The forever-loop

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Forever loop wrapping a timing control.
TEST(ParserSection12, ForeverWithTimingControl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    forever begin\n"
              "      @(posedge clk);\n"
              "      x = ~x;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
