#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PrimaryParsing, PrimaryThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ImplicitClassHandleThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ImplicitClassHandleThisMember) {
  auto r = Parse("module m; initial x = this.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassParsing, ThisExpression) {
  auto r = Parse(
      "class MyClass;\n"
      "  int data;\n"
      "  function void set(int data);\n"
      "    this.data = data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ClassParsing, ThisKeywordPropertyAccess) {
  EXPECT_TRUE(
      ParseOk("class MyClass;\n"
              "  int value;\n"
              "  function void set_value(int value);\n"
              "    this.value = value;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ThisParsing, ThisDisambiguationInConstructor) {
  auto r = Parse(
      "class Demo;\n"
      "  integer x;\n"
      "  function new(integer x);\n"
      "    this.x = x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  auto* ctor = cls->members[1];
  EXPECT_EQ(ctor->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(ctor->method->name, "new");
}

TEST(ThisParsing, ThisChainedMemberAccess) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int a;\n"
              "  function int get_a();\n"
              "    return this.a;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ThisParsing, ThisMethodCallChain) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function C get_self();\n"
              "    return this;\n"
              "  endfunction\n"
              "endclass\n"));
}

}  // namespace
