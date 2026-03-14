#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameElaboration, ClassVariableDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p1;\n"
             "endmodule\n"));
}

TEST(ClassAssignRenameElaboration, HandleAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p1, p2;\n"
             "    p1 = new;\n"
             "    p2 = p1;\n"
             "  end\n"
             "endmodule\n"));
}

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

}  // namespace
