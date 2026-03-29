#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ChainedConstructorParsing, ExtendsWithArgs) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Child extends Base(1, 2);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ChainedConstructorParsing, ExtendsArgsStored) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class EtherPacket extends Base(5);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->extends_args.size(), 1u);
}

TEST(ChainedConstructorParsing, ThreeLevelChaining) {
  EXPECT_TRUE(
      ParseOk("class A;\n"
              "  function new();\n"
              "  endfunction\n"
              "endclass\n"
              "class B extends A;\n"
              "  function new();\n"
              "    super.new();\n"
              "  endfunction\n"
              "endclass\n"
              "class C extends B;\n"
              "  function new();\n"
              "    super.new();\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ChainedConstructorParsing, ExtendsWithDefault) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class A extends Base(default);\n"
      "  function new(default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->extends_has_default);
}

TEST(ChainedConstructorParsing, ImplicitSuperNewNoConstructor) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  function new();\n"
              "  endfunction\n"
              "endclass\n"
              "class Child extends Base;\n"
              "  int x;\n"
              "endclass\n"));
}

TEST(ChainedConstructorParsing, SuperNewDefault) {
  ParseOk(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new(default);\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ChainedConstructorParsing, ConstructorDefaultArg) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  ASSERT_EQ(members[0]->method->func_args.size(), 1u);
  EXPECT_TRUE(members[0]->method->func_args[0].is_default);
}

TEST(ChainedConstructorParsing, ConstructorMixedArgsWithDefault) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(int size, default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& args = r.cu->classes[0]->members[0]->method->func_args;
  ASSERT_EQ(args.size(), 2u);
  EXPECT_FALSE(args[0].is_default);
  EXPECT_EQ(args[0].name, "size");
  EXPECT_TRUE(args[1].is_default);
}

TEST(ChainedConstructorParsing, ConstructorDefaultBeforeArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, bit enable);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto& args = r.cu->classes[0]->members[0]->method->func_args;
  ASSERT_EQ(args.size(), 2u);
  EXPECT_TRUE(args[0].is_default);
  EXPECT_FALSE(args[1].is_default);
}

TEST(ChainedConstructorParsing, ErrorDuplicateDefaultInConstructorArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, int x, default);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ChainedConstructorParsing, ExtendsWithMultipleArgs) {
  auto r = Parse(
      "class Base; endclass\n"
      "class Derived extends Base(1, 2, 3);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->extends_args.size(), 3u);
}

TEST(ChainedConstructorParsing, ExtendsEmptyParens) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->extends_args.empty());
  EXPECT_FALSE(r.cu->classes[1]->extends_has_default);
}

TEST(ChainedConstructorParsing, SuperNewDefaultStoresIdentifier) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new(default);\n"
      "    super.new(default);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  auto* ctor = r.cu->classes[1]->members[0]->method;
  ASSERT_EQ(ctor->func_body_stmts.size(), 1u);
  auto* call_stmt = ctor->func_body_stmts[0];
  ASSERT_NE(call_stmt->expr, nullptr);
  ASSERT_EQ(call_stmt->expr->args.size(), 1u);
  EXPECT_EQ(call_stmt->expr->args[0]->text, "default");
}

}  // namespace
