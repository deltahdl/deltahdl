#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, ModuleWithIntegerLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] x = 8'hFF;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithRealLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  real r = 3.14;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithStringLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithAttributeElaborates) {
  EXPECT_TRUE(
      ElabOk("(* synthesis *) module t;\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithTimeLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial #10ns;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithUnbasedUnsizedLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [15:0] x;\n"
             "  assign x = '1;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithArrayLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr [0:1];\n"
             "  initial arr = '{0, 1};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithStructureLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab_t;\n"
             "  ab_t s;\n"
             "  initial s = '{0, 1};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, ModuleWithBuiltinMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int q[$];\n"
             "  int sz;\n"
             "  initial sz = q.size();\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, AllFourAreasElaborate) {
  EXPECT_TRUE(
      ElabOk("(* optimize *) module t;\n"
             "  logic [7:0] data = 8'hAB;\n"
             "  real pi = 3.14;\n"
             "  initial $display(\"all areas: %d\", data);\n"
             "endmodule\n"));
}

}  // namespace
