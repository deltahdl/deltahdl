#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA815, SuperInDerivedMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = value * value;\n"
             "  endfunction\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer value;\n"
             "  function integer delay();\n"
             "    delay = super.delay() + value * super.value;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

TEST(ElabA815, SuperInModuleBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    x = super.val;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ElabA815, SuperInStaticMethodError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  static function int get_x();\n"
             "    return super.x;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ElabA815, SuperNewInConstructorOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function new();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function new();\n"
             "    super.new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

}  // namespace
