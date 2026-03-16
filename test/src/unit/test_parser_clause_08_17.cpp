#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ClassParsing, ExtendsWithArgs) {
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

}  // namespace
