// §14.9: Interfaces and clocking blocks

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Clocking block in an interface (valid scope per LRM).
TEST(ParserSection19, ClockingBlockScope_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface bus_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

}  // namespace
