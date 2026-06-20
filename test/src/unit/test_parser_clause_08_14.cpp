#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OverriddenMemberParsing, SubclassOverridesProperty) {
  auto r = Parse(
      "class Packet;\n"
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
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Packet");
}

TEST(OverriddenMemberParsing, SubclassAssignedToBaseVariable) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
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

TEST(OverriddenMemberParsing, AccessThroughBaseClassVariable) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
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

TEST(OverriddenMemberParsing, MultiLevelOverrideAccessThroughBase) {
  EXPECT_TRUE(
      ParseOk("class A;\n"
              "  integer x = 1;\n"
              "endclass\n"
              "class B extends A;\n"
              "  integer x = 2;\n"
              "endclass\n"
              "class C extends B;\n"
              "  integer x = 3;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    C c;\n"
              "    A a;\n"
              "    c = new;\n"
              "    a = c;\n"
              "    automatic integer j;\n"
              "    j = a.x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(OverriddenMemberParsing, NonOverriddenMemberThroughBaseHandle) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  integer x = 5;\n"
              "endclass\n"
              "class LinkedPacket extends Packet;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    LinkedPacket lp;\n"
              "    Packet p;\n"
              "    lp = new;\n"
              "    p = lp;\n"
              "    automatic integer j;\n"
              "    j = p.x;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
