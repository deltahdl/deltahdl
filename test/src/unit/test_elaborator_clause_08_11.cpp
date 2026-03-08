#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA811, ThisInModuleInitialBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = this.data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ElabA811, ThisInModuleAlwaysBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  always @(posedge clk) begin\n"
             "    automatic int x;\n"
             "    x = this.val;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ElabA811, ThisInModuleFunctionError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function int get_val();\n"
             "    return this.val;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ElabA811, ThisInNonStaticClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Demo;\n"
             "  integer x;\n"
             "  function new(integer x);\n"
             "    this.x = x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Demo d;\n"
             "endmodule\n"));
}

TEST(ElabA811, ThisInRegularMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int data;\n"
             "  function int get_data();\n"
             "    return this.data;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ElabA811, NoThisReferencesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = 42;\n"
             "  end\n"
             "endmodule\n"));
}

}
