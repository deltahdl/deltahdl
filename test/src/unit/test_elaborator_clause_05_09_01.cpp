#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, StringWithNamedEscapeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\\nworld\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringWithOctalEscapeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  byte c;\n"
             "  initial c = \"\\101\";\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringWithHexEscapeElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  byte c;\n"
             "  initial c = \"\\x41\";\n"
             "endmodule\n"));
}

}  // namespace
