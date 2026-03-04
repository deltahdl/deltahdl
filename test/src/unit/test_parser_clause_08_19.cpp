#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection8, ConstProperty) {
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

TEST(ParserSection8, StaticConstProperty) {
  auto r = Parse(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_TRUE(cls->members[0]->is_const);
}

TEST(SourceText, ClassConstProperty) {
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

}
