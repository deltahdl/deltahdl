#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ParserSection8, ExtendsScopedName) {
  auto r = Parse(
      "class Child extends pkg::Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);

  EXPECT_EQ(r.cu->classes[0]->name, "Child");
}

TEST(Parser, ClassExtends) {
  auto r = Parse("class child extends parent; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "child");
  EXPECT_EQ(cls->base_class, "parent");
}

TEST(SourceText, ClassWithExtends) {
  auto r = Parse("class Child extends Parent; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Parent");
}

TEST(SourceText, ClassWithFinal) {
  auto r = Parse("class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(ParserSection8, ClassExtendsBase) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "Base");
  EXPECT_TRUE(r.cu->classes[0]->base_class.empty());
}

TEST(ParserSection8, ClassExtendsDerived) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->name, "Derived");
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ParserA813, SubclassInheritsAndAddsMembers) {
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

TEST(ParserA813, FinalClassWithExtends) {
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

TEST(ParserA813, ExtendsWithConstructorArgs) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base(42);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[1];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_GE(cls->extends_args.size(), 1u);
}

TEST(ParserA813, ExtendsWithDefault) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Derived extends Base(default);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[1]->extends_has_default);
}

TEST(ParserA813, SingleInheritanceChain) {
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

}  // namespace
