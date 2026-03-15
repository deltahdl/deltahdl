#include "fixture_elaborator.h"

namespace {

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
