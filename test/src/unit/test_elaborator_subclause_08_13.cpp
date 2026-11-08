#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(InheritanceElaboration, ExtendFinalClassFromAnyScopeIsAnError) {
  ElabFixture f;
  ElabOk(
      "class :final F; endclass\n"
      "package p;\n"
      "  class P extends F; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class :final G; endclass\n"
      "  class M extends G; endclass\n"
      "  class O;\n"
      "    class N extends F; endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (const int kLine : {3, 7, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "cannot extend a class declared ':final'", kLine,
                              "8.13"))
        << kLine;
  }
}

TEST(InheritanceElaboration, ABaseIsTheClassItsOwnScopeResolves) {
  ElabFixture f;
  ElabOk(
      "class :final J; endclass\n"
      "module a;\n"
      "  class :final K; endclass\n"
      "endmodule\n"
      "module b;\n"
      "  class K; endclass\n"
      "  class D extends K; endclass\n"
      "  class J; endclass\n"
      "  class DJ extends J; endclass\n"
      "endmodule\n"
      "module c;\n"
      "  class :final K; endclass\n"
      "  class E extends K; endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMessage = "cannot extend a class declared ':final'";
  EXPECT_TRUE(ReportedError(diags, kMessage, 13, "8.13"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 7, "8.13"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 9, "8.13"));
}

}  // namespace
