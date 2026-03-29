#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassCastElaboration, SubclassToSuperclassAssignOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int i;\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  int j;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    LinkedPacket lp;\n"
             "    lp = new;\n"
             "    p = lp;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastSuperToSubclassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Base b;\n"
             "    Derived d;\n"
             "    d = new;\n"
             "    b = d;\n"
             "    $cast(d, b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastAsFunctionOk) {
  EXPECT_TRUE(
      ElabOk("class Base; int x; endclass\n"
             "class Derived extends Base; int y; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Base b;\n"
             "    Derived d;\n"
             "    int ok;\n"
             "    d = new;\n"
             "    b = d;\n"
             "    ok = $cast(d, b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Derived extends Base; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    $cast(d, null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, DirectSuperclassToSubclassAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    b = new;\n"
      "    d = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassCastElaboration, UnrelatedClassTypesAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    A a;\n"
      "    B b;\n"
      "    a = new;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ClassCastElaboration, DeepHierarchyUpcastOk) {
  EXPECT_TRUE(
      ElabOk("class Grand; endclass\n"
             "class Mid extends Grand; endclass\n"
             "class Leaf extends Mid; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Grand g;\n"
             "    Leaf l;\n"
             "    l = new;\n"
             "    g = l;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastDeepHierarchyDowncastOk) {
  EXPECT_TRUE(
      ElabOk("class Grand; endclass\n"
             "class Mid extends Grand; endclass\n"
             "class Leaf extends Mid; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Grand g;\n"
             "    Leaf l;\n"
             "    l = new;\n"
             "    g = l;\n"
             "    $cast(l, g);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
