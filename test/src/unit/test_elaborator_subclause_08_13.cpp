#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// Elaborator::ValidateFinalClassExtension in
// src/elaborator/elaborator_validate_class_members.cpp has two sites carrying
// this message: one for a class extending the built-in `process`, one for a
// class whose named base carries `:final`. A user-written `:final` base reaches
// the second, and the report stands at the extending class's own declaration,
// which the site passes as `cls->range.start`.
TEST(InheritanceElaboration, ExtendFinalClassError) {
  ElabFixture f;
  ElabOk(
      "class :final TopPacket;\n"
      "endclass\n"
      "class BrokenPacket extends TopPacket;\n"
      "endclass\n"
      "module m;\n"
      "  BrokenPacket b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 3,
                            "8.13"));
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
  ElabFixture f;
  ElabOk(
      "class A;\n"
      "endclass\n"
      "class :final B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 5,
                            "8.13"));
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

// Elaborator::BreakClassInheritanceCycles in
// src/elaborator/elaborator_validate_class_overrides.cpp: a class extending
// itself has no original base class for its superclasses to begin with, and
// it is reported at its own declaration rather than sending every later walk
// up its chain of base classes around the cycle without end.
TEST(InheritanceElaboration, ClassExtendingItselfError) {
  ElabFixture f;
  ElabOk(
      "class A extends A;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 1, "8.13"));
}

// Two classes extending each other close one cycle, reported once at the class
// the walk set out from; the extends clause it drops leaves the other class a
// chain that ends.
TEST(InheritanceElaboration, MutualExtensionCycleReportedOnce) {
  ElabFixture f;
  ElabOk(
      "class A extends B;\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 1, "8.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "class 'B' inherits from itself", 3, "8.13"));
}

// A class extending into a cycle it is not on is not reported: its walk stops
// where it meets the cycle, and the cycle's own class is reported, here one
// declared inside a module.
TEST(InheritanceElaboration, CycleReachedFromOutsideReportsItsOwnClass) {
  ElabFixture f;
  ElabOk(
      "class C extends A;\n"
      "endclass\n"
      "module t;\n"
      "  class A extends B;\n"
      "  endclass\n"
      "  class B extends A;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 4, "8.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "class 'C' inherits from itself", 1, "8.13"));
}

// A class nested in another (§8.23) is found by no scope's list of classes,
// and a cycle through its extends clause is reported all the same.
TEST(InheritanceElaboration, NestedClassExtendingItselfError) {
  ElabFixture f;
  ElabOk(
      "class Outer;\n"
      "  class In extends In;\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'In' inherits from itself", 2, "8.13"));
}

}  // namespace
