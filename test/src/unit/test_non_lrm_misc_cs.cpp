// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull0\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseOk("`celldefine\n"
              "module inv(output y, input a);\n"
              "  assign y = ~a;\n"
              "endmodule\n"
              "`endcelldefine\n"));
}

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
