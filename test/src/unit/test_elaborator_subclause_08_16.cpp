#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §8.16 states "It shall be illegal to directly assign a variable of a
// superclass type to a variable of one of its subclass types". The rejection is
// reported under §8.4, which is where the standard states that an object handle
// admits only the assignment of a class object assignment compatible with the
// target; §8.16 settles which handles are compatible rather than making the
// assignment illegal itself.
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    8, "8.4"));
}

// §8.16 says nothing about two class types outside one inheritance tree; the
// rule rejecting this source is §8.4's list of the operators valid on an object
// handle, which admits "Assignment of a class object whose class data type is
// assignment compatible with the target class object" and no other assignment.
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    8, "8.4"));
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
