#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(ClassAssignRenameParsing, ShallowCopyInDeclaration) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
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

// §8.12: it shall be illegal to use a typed constructor call for a shallow
// copy. The plain shallow-copy form `new src` reads the trailing source-object
// identifier as the object to copy, but a typed constructor call `C::new`
// parses as a scope-resolved reference to the class's `new`; the grammar
// provides no way to attach a copy-source argument to it. So `C::new src` has
// no valid parse, and the trailing identifier is rejected -- the illegality is
// enforced structurally at parse time rather than by a later semantic check.
// The plain `c2 = new c1;` form (covered by ShallowCopyNewIdentifier) parses
// cleanly, isolating the difference to the `C::` typed prefix.
TEST(ClassAssignRenameParsing, TypedConstructorShallowCopyRejected) {
  EXPECT_FALSE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    C c1, c2;\n"
              "    c1 = new;\n"
              "    c2 = C::new c1;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
