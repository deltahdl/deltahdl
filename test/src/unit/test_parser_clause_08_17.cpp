#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ParserSection8, ExtendsWithArgs) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Child extends Base(1, 2);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

TEST(ParserSection8, ConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

TEST(ParserSection8, SuperNewExpression) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

TEST(ParserSection8, ConstructorChainingDefault) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x = 0);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

// §8.17: extends specifier with arguments stores extends_args.
TEST(ParserA817, ExtendsArgsStored) {
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

// §8.17: Constructor chaining — three-level hierarchy parses OK.
TEST(ParserA817, ThreeLevelChaining) {
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

// §8.17: super.new with arguments parses.
TEST(ParserA817, SuperNewWithMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  function new(string name, int id);\n"
              "  endfunction\n"
              "endclass\n"
              "class Child extends Base;\n"
              "  function new();\n"
              "    super.new(\"foo\", 42);\n"
              "  endfunction\n"
              "endclass\n"));
}

// §8.17: extends with 'default' keyword parses.
TEST(ParserA817, ExtendsWithDefault) {
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

// §8.17: No constructor in subclass (implicit super.new) parses OK.
TEST(ParserA817, ImplicitSuperNewNoConstructor) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  function new();\n"
              "  endfunction\n"
              "endclass\n"
              "class Child extends Base;\n"
              "  int x;\n"
              "endclass\n"));
}

TEST(ParserClause08_03, ConstructorMixedArgsWithDefault) {
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

TEST(ParserClause08_03, ConstructorDefaultBeforeArgs) {
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

}  // namespace
