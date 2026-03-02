// §16.14.6: Embedding concurrent assertions in procedural code

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using VerifyParseTest = ProgramTestParse;

namespace {

// =============================================================================
// Section 16.5.1 -- Named concurrent assertions (label: assert property)
// Named assertions in procedural context use statement labels.
// =============================================================================
// Named assert property inside an always block.
TEST(ParserSection16, Sec16_5_1_NamedAssertInAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    check_req: assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Concurrent assertions in procedural context
// =============================================================================
// Assert property inside an always block (procedural concurrent assertion).
TEST(ParserSection16, Sec16_5_1_AssertPropertyInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
