#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassConstructorElaboration, ExplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer command;\n"
             "  function new();\n"
             "    command = 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "  function new(int cmd, int addr);\n"
             "    command = cmd;\n"
             "    address = addr;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new(1, 2);\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorWithDefaultArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  bit [12:0] address;\n"
             "  int cmd_time;\n"
             "  function new(int cmd = 0, bit [12:0] adrs = 0, int t = 0);\n"
             "    command = cmd;\n"
             "    address = adrs;\n"
             "    cmd_time = t;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial p = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ImplicitConstructorDerivedElaborates) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  function new();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Child c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorStaticError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  static function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, ConstructorVirtualError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  virtual function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, PropertyWithExplicitDefaultElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x = 5;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = new;\n"
             "endmodule\n"));
}

TEST(ClassConstructorElaboration, DerivedClassConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int b;\n"
             "  function new();\n"
             "    b = 1;\n"
             "  endfunction\n"
             "endclass\n"
             "class Child extends Base;\n"
             "  int c;\n"
             "  function new();\n"
             "    super.new();\n"
             "    c = 2;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Child ch;\n"
             "  initial ch = new;\n"
             "endmodule\n"));
}

}  // namespace
