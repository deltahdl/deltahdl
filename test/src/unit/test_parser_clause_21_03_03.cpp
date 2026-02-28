// §21.3.3: Formatting data to a string

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// LRM section 21.3.3 -- Formatting data to a string ($swrite, $sformat,
//                        $sformatf)
// ============================================================================
TEST(ParserSection21, SwriteBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $swrite(s, \"value=%d\", 42);\n"
              "endmodule\n"));
}

}  // namespace
