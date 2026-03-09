#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA84, ImplicitClassHandleSuper) {
  auto r = Parse("module m; initial x = super; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, MethodCallRootSuper) {
  auto r = Parse(
      "module m;\n"
      "  initial begin super.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SourceText, ClassConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
  EXPECT_EQ(r.cu->classes[1]->members[0]->method->name, "new");
}

TEST(ParserA815, SuperMemberAccess) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  integer value;\n"
              "  function integer delay();\n"
              "    delay = value * value;\n"
              "  endfunction\n"
              "endclass\n"
              "class LinkedPacket extends Packet;\n"
              "  integer value;\n"
              "  function integer delay();\n"
              "    delay = super.delay() + value * super.value;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ParserA815, SuperNewInConstructor) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  function new();\n"
              "  endfunction\n"
              "endclass\n"
              "class Derived extends Base;\n"
              "  function new();\n"
              "    super.new();\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ParserA815, SuperSuperError) {
  auto r = Parse(
      "class A;\n"
      "  int count;\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "  function int get_count();\n"
      "    return super.super.count;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserA815, SuperMethodCall) {
  auto r = Parse(
      "class Base;\n"
      "  function int foo();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int foo();\n"
      "    return super.foo() + 1;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA815, SuperNewWithArgs) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "  function new(int x);\n"
      "    this.x = x;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "  function new(int x, int y);\n"
      "    super.new(x);\n"
      "    this.y = y;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
