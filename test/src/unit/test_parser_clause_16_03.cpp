// §16.3: Immediate assertions

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// =============================================================================
// Gap-filling tests identified by coverage proof
// =============================================================================
// concurrent_assertion_item ::= [ block_identifier : ]
// concurrent_assertion_statement
TEST(ParserA210, ConcurrentAssertionItem_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    my_check: assert(a == b);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
