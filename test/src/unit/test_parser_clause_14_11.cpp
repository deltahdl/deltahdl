// §14.11: Cycle delay: ##

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.11 cycle_delay — ## identifier
// =============================================================================
TEST(ParserA611, CycleDelayIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##n 8'h42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
