#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OverriddenMemberElaboration, SubclassOverriddenPropertyOk) {
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

TEST(OverriddenMemberElaboration, SubclassHandleToBaseVariableOk) {
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

TEST(OverriddenMemberElaboration, BaseClassMemberAccessOk) {
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
