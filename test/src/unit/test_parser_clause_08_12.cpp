#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameParsing, ClassNewCopy) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c1, c2;\n"
      "  initial c2 = new c1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassAssignRenameParsing, ShallowCopy) {
  auto r = Parse(
      "module m;\n"
      "  class Packet;\n"
      "    int data;\n"
      "  endclass\n"
      "  initial begin\n"
      "    Packet p1, p2;\n"
      "    p1 = new;\n"
      "    p2 = new p1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassAssignRenameParsing, HandleAssignment) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
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

TEST(ClassAssignRenameParsing, ShallowCopyNewIdentifier) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C c1, c2;\n"
      "    c1 = new;\n"
      "    c2 = new c1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassAssignRenameParsing, ChainedMemberAccess) {
  EXPECT_TRUE(
      ParseOk("class A;\n"
              "  int j;\n"
              "endclass\n"
              "class B;\n"
              "  int i;\n"
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

TEST(ClassAssignRenameParsing, PropertyInitInClassBody) {
  auto r = Parse(
      "class baseA;\n"
      "  integer j = 5;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ClassAssignRenameParsing, ClassContainingClassProperty) {
  EXPECT_TRUE(
      ParseOk("class baseA;\n"
              "  integer j = 5;\n"
              "endclass\n"
              "class B;\n"
              "  integer i = 1;\n"
              "  baseA a;\n"
              "endclass\n"));
}

TEST(ClassAssignRenameParsing, ShallowCopyWithData) {
  auto r = Parse(
      "class C;\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    a = new;\n"
      "    b = new a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassAssignRenameParsing, ShallowCopyInDeclaration) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c1;\n"
      "  initial begin C c2 = new c1; end\n"
      "endmodule\n"));
}

TEST(ClassAssignRenameParsing, DeepChainedMemberAccess) {
  EXPECT_TRUE(
      ParseOk("class Node;\n"
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

TEST(ClassAssignRenameParsing, ShallowCopyExtendedClass) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
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

TEST(ClassAssignRenameParsing, HandleAssignmentAfterPropertyMutation) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    C p1, p2;\n"
              "    p1 = new;\n"
              "    p1.x = 5;\n"
              "    p2 = p1;\n"
              "    p2.x = 10;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
