#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ThisElaboration, ThisInModuleInitialBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = this.data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInModuleAlwaysBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  always @(posedge clk) begin\n"
             "    automatic int x;\n"
             "    x = this.val;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInModuleFunctionError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function int get_val();\n"
             "    return this.val;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInNonStaticClassMethodOk) {
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

TEST(ThisElaboration, ThisInRegularMethodOk) {
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

TEST(ThisElaboration, NoThisReferencesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = 42;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInModuleTaskError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  task do_work();\n"
             "    automatic int x;\n"
             "    x = this.data;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInClassTaskOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int data;\n"
             "  task set_data(int d);\n"
             "    this.data = d;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, ThisInConstructorOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int a;\n"
             "  int b;\n"
             "  function new(int a, int b);\n"
             "    this.a = a;\n"
             "    this.b = b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ThisElaboration, BareThisInModuleInitialError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = this;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ThisElaboration, BareThisInClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function C get_self();\n"
             "    return this;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
