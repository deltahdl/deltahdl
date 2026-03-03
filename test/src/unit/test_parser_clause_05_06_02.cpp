// §5.6.2: Keywords

#include "fixture_parser.h"

using namespace delta;

namespace {

// =========================================================================
// Keywords are reserved words
// =========================================================================
TEST(ParserCh501, Sec5_1_KeywordsAreReserved) {
  // module, endmodule, wire, logic, assign, initial, begin, end, if, else
  // are all reserved keywords that parse correctly.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  logic l;\n"
              "  assign w = 0;\n"
              "  initial begin\n"
              "    if (l) w = 1;\n"
              "    else w = 0;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
