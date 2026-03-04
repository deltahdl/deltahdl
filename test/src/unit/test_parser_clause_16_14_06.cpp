#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(ParserSection16, Sec16_5_1_NamedAssertInAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    check_req: assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_AssertPropertyInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
