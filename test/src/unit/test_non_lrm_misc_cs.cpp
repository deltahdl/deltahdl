// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// LRM section 22.13 -- `__FILE__ and `__LINE__
// ============================================================================
TEST(ParserSection22, FileDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"File: %s\", `__FILE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Line: %0d\", `__LINE__);\n"
              "endmodule\n"));
}

}  // namespace
