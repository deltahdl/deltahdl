#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.14: Subclass with overridden property elaborates OK.
TEST(ElabA814, SubclassOverriddenPropertyOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer i = 1;\n"
             "  function integer get();\n"
             "    get = i;\n"
             "  endfunction\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer i = 2;\n"
             "  function integer get();\n"
             "    get = -i;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

// §8.14: Subclass handle assigned to base class variable elaborates.
TEST(ElabA814, SubclassHandleToBaseVariableOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer i;\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer i;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    LinkedPacket lp;\n"
             "    Packet p;\n"
             "    lp = new;\n"
             "    p = lp;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.14: Base class access through base class variable elaborates.
TEST(ElabA814, BaseClassMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  integer i = 1;\n"
             "  function integer get();\n"
             "    get = i;\n"
             "  endfunction\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  integer i = 2;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    LinkedPacket lp;\n"
             "    Packet p;\n"
             "    automatic integer j;\n"
             "    lp = new;\n"
             "    p = lp;\n"
             "    j = p.i;\n"
             "    j = p.get();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
