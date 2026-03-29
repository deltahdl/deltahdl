#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameElaboration, ShallowCopyOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c1, c2;\n"
             "    c1 = new;\n"
             "    c2 = new c1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, ChainedMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "  int j;\n"
             "endclass\n"
             "class B;\n"
             "  A a;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    B b1;\n"
             "    b1 = new;\n"
             "    b1.a = new;\n"
             "    b1.a.j = 50;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, HandleAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C p1, p2;\n"
             "    p1 = new;\n"
             "    p2 = p1;\n"
             "    p2.x = 10;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, ShallowCopyWithInheritanceOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int j;\n"
             "endclass\n"
             "class Ext extends Base;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Ext e;\n"
             "    Base b;\n"
             "    e = new;\n"
             "    b = e;\n"
             "    Base b2;\n"
             "    b2 = new b;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, ShallowCopyInDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c1;\n"
             "    c1 = new;\n"
             "    C c2 = new c1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, DeepChainedMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Node;\n"
             "  int val;\n"
             "  Node next;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Node p;\n"
             "    p = new;\n"
             "    p.next = new;\n"
             "    p.next.next = new;\n"
             "    p.next.next.val = 99;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
