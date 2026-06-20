#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, ModuleWithStringLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, TripleQuotedStringElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"\"\"hello\"\"\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringAssignmentToByteElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  byte c;\n"
             "  initial c = \"A\";\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringAssignmentToPackedArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  bit [8*5:1] s;\n"
             "  initial s = \"Hello\";\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, EmptyStringElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"\");\n"
             "endmodule\n"));
}

}  // namespace
