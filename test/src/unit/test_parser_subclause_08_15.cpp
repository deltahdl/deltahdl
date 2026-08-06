#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SuperParsing, ImplicitClassHandleSuper) {
  auto r = Parse("module m; initial x = super; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SuperParsing, MethodCallRootSuper) {
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

TEST(SuperParsing, ClassConstructorSuperNew) {
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

TEST(SuperParsing, SuperMemberAccess) {
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

TEST(SuperParsing, SuperSuperError) {
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

TEST(SuperParsing, SuperPropertyAssignment) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  int x;\n"
              "endclass\n"
              "class Derived extends Base;\n"
              "  int x;\n"
              "  function void set_base();\n"
              "    super.x = 5;\n"
              "  endfunction\n"
              "endclass\n"));
}

}  // namespace
