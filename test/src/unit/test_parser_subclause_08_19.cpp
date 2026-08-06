#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConstantClassPropertyParsing, ConstPropertyVerifiesName) {
  auto r = Parse(
      "class MyClass;\n"
      "  const int MAX = 100;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_const);
  EXPECT_EQ(cls->members[0]->name, "MAX");
}

TEST(ConstantClassPropertyParsing, ConstAndStaticConstProperties) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  const static int SMAX = 200;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_EQ(members[0]->name, "MAX");
  EXPECT_NE(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_TRUE(members[1]->is_static);
}

TEST(ConstantClassPropertyParsing, ConstPropertyWithInitExpression) {
  auto r = Parse(
      "class Jumbo_Packet;\n"
      "  const int max_size = 9 * 1024;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_NE(m->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, InstanceConstantNoInitializer) {
  auto r = Parse(
      "class Big_Packet;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 4096;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_EQ(m->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, StaticConstPropertyWithInitializer) {
  auto r = Parse(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_static);
  EXPECT_TRUE(m->is_const);
  EXPECT_NE(m->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, GlobalAndInstanceConstInSameClass) {
  auto r = Parse(
      "class Packet;\n"
      "  const int max_size = 1024;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 512;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_NE(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_EQ(members[1]->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, ConstQualifierOrderReversed) {
  auto r = Parse(
      "class C;\n"
      "  const static int A = 1;\n"
      "  static const int B = 2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_TRUE(members[0]->is_static);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_TRUE(members[1]->is_static);
}

TEST(ConstantClassPropertyParsing, ConstWithLocalQualifier) {
  auto r = Parse(
      "class C;\n"
      "  local const int X = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_TRUE(m->is_local);
  EXPECT_NE(m->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, ConstWithProtectedQualifier) {
  auto r = Parse(
      "class C;\n"
      "  protected const int X = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_TRUE(m->is_protected);
  EXPECT_NE(m->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, MultipleInstanceConstants) {
  auto r = Parse(
      "class C;\n"
      "  const int a;\n"
      "  const int b;\n"
      "  function new(int x, int y);\n"
      "    a = x;\n"
      "    b = y;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_EQ(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_EQ(members[1]->init_expr, nullptr);
}

TEST(ConstantClassPropertyParsing, ConstByteProperty) {
  auto r = Parse(
      "class C;\n"
      "  const byte tag = 8'hFF;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_NE(m->init_expr, nullptr);
}

}  // namespace
