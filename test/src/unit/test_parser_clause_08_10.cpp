#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection13, Sec13_8_MixedStaticFuncAndTask) {
  auto r = Parse(
      "virtual class Utils#(parameter N = 4);\n"
      "  static function int max_val();\n"
      "    return (1 << N) - 1;\n"
      "  endfunction\n"
      "  static task report();\n"
      "    $display(\"N=%0d\", N);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(ParserSection13, Sec13_8_StaticMethodNoArgs) {
  auto r = Parse(
      "virtual class Constants#(parameter N = 32);\n"
      "  static function int zero();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection13, Sec13_8_MultiArgParameterizedWidth) {
  EXPECT_TRUE(
      ParseOk("virtual class Arith#(parameter W = 16);\n"
              "  static function logic [W-1:0] add(\n"
              "      input logic [W-1:0] a,\n"
              "      input logic [W-1:0] b);\n"
              "    return a + b;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ParserA810, StaticFunctionDeclaration) {
  auto r = Parse(
      "class id;\n"
      "  static int current;\n"
      "  static function int next_id();\n"
      "    return current;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  auto* m = cls->members[1];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_static);
  EXPECT_EQ(m->method->name, "next_id");
}

TEST(ParserA810, StaticTaskDeclaration) {
  auto r = Parse(
      "class Logger;\n"
      "  static task log_msg();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(cls->members[0]->is_static);
}

TEST(ParserA810, StaticVirtualFunctionError) {
  auto r = Parse(
      "class C;\n"
      "  static virtual function int foo();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserA810, StaticVirtualTaskError) {
  auto r = Parse(
      "class C;\n"
      "  virtual static task bar();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserA810, StaticMethodClassScopeCall) {
  ParseOk(
      "class id;\n"
      "  static function int next_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = id::next_id();\n"
      "  end\n"
      "endmodule\n");
}

TEST(ParserA810, StaticMethodInstanceDotCall) {
  ParseOk(
      "class C;\n"
      "  static function int helper();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = c.helper();\n"
      "  end\n"
      "endmodule\n");
}

TEST(ParserA810, StaticMethodVsStaticLifetime) {
  auto r = Parse(
      "class TwoTasks;\n"
      "  static task t1();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);

  EXPECT_TRUE(cls->members[0]->is_static);
}

}  // namespace
