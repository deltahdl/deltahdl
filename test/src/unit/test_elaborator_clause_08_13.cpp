#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InheritanceElaboration, ClassExtendsOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, ExtendFinalClassError) {
  EXPECT_FALSE(
      ElabOk("class :final TopPacket;\n"
             "endclass\n"
             "class BrokenPacket extends TopPacket;\n"
             "endclass\n"
             "module m;\n"
             "  BrokenPacket b;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, FinalClassAloneOk) {
  EXPECT_TRUE(
      ElabOk("class :final Sealed;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  Sealed s;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, MultiLevelInheritanceOk) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "endclass\n"
             "class B extends A;\n"
             "endclass\n"
             "class C extends B;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, ExtendFinalInChainError) {
  EXPECT_FALSE(
      ElabOk("class A;\n"
             "endclass\n"
             "class :final B extends A;\n"
             "endclass\n"
             "class C extends B;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, SubclassWithAdditionalMembersOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  LinkedPacket next;\n"
             "  function LinkedPacket get_next();\n"
             "    get_next = next;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, FinalDerivedClassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class :final Leaf extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Leaf l;\n"
             "endmodule\n"));
}

}  // namespace
