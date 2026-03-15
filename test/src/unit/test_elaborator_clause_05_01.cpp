#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, ModuleWithIntegerLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] x = 8'hFF;\n"
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
