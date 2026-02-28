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

TEST(ParserSection21, SwritebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial begin\n"
              "    $swriteb(s, val);\n"
              "    $swriteh(s, val);\n"
              "    $swriteo(s, val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, SformatBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string s;\n"
              "  initial $sformat(s, \"data is %d\", 123);\n"
              "endmodule\n"));
}

}  // namespace
