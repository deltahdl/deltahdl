#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(AssertionParsing, NamedAssertInAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    check_req: assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssertionParsing, AssertPropertyInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
