#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(InheritanceParsing, ExtendsScopedName) {
  auto r = Parse(
      "class Child extends pkg::Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);

  EXPECT_EQ(r.cu->classes[0]->name, "Child");
  EXPECT_EQ(r.cu->classes[0]->base_class, "Base");
  EXPECT_EQ(r.cu->classes[0]->base_class_scope, "pkg");
}

TEST(InheritanceParsing, ClassExtends) {
  auto r = Parse("class child extends parent; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "child");
  EXPECT_EQ(cls->base_class, "parent");
  EXPECT_TRUE(cls->base_class_scope.empty());
}

TEST(InheritanceParsing, SubclassInheritsAndAddsMembers) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function int get();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n"
      "class LinkedPacket extends Packet;\n"
      "  LinkedPacket next;\n"
      "  function LinkedPacket get_next();\n"
      "    get_next = next;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* lp = r.cu->classes[1];
  EXPECT_EQ(lp->name, "LinkedPacket");
  EXPECT_EQ(lp->base_class, "Packet");
  EXPECT_GE(lp->members.size(), 2u);
}

TEST(InheritanceParsing, SingleInheritanceChain) {
  auto r = Parse(
      "class A;\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 3u);
  EXPECT_TRUE(r.cu->classes[0]->base_class.empty());
  EXPECT_EQ(r.cu->classes[1]->base_class, "A");
  EXPECT_EQ(r.cu->classes[2]->base_class, "B");
}

TEST(InheritanceParsing, FinalClassParsed) {
  auto r = Parse("class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(InheritanceParsing, FinalClassWithExtends) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class :final TopPacket extends Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->is_final);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(InheritanceParsing, NonFinalDerivedClassIsFinalFalse) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->classes[1]->is_final);
}

TEST(InheritanceParsing, AClassNamingTwoBasesIsReportedInEveryPlace) {
  auto r = Parse(
      "class A; function new(int x); endfunction endclass\n"
      "class B; endclass\n"
      "class P #(int N = 1); endclass\n"
      "interface class IA; endclass\n"
      "interface class IB; endclass\n"
      "interface class IC extends IA, IB; endclass\n"
      "module m;\n"
      "  class M1 extends A, B; endclass\n"
      "  class M2 extends A; function new(); super.new(1); endfunction "
      "endclass\n"
      "endmodule\n"
      "package pk;\n"
      "  class K1 extends P #(1), B; endclass\n"
      "  class K2 extends P #(1); endclass\n"
      "endpackage\n"
      "program pr;\n"
      "  class R1 extends A(1), B; endclass\n"
      "  class R2 extends A(1); endclass\n"
      "endprogram\n"
      "interface itf;\n"
      "  virtual class F1 extends A, B; endclass\n"
      "  virtual class F2 extends A(2); endclass\n"
      "endinterface\n"
      "class U1 extends IA, IB; endclass\n"
      "class U2 extends A(3) implements IA, IB; endclass\n");
  for (const int kLine : {8, 12, 16, 20, 23}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a class extends one class type; only an "
                              "interface class extends several",
                              kLine, "A.1.2"))
        << kLine;
  }
  for (const int kLine : {6, 9, 13, 17, 21, 24}) {
    EXPECT_FALSE(ErrorOnLine(r.diags, kLine)) << kLine;
  }
}

}  // namespace
