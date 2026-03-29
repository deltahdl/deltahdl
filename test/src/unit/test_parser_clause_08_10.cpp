#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(StaticMethodParsing, StaticMethodClassScopeCall) {
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

TEST(StaticMethodParsing, StaticMethodInstanceDotCall) {
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

TEST(StaticMethodParsing, StaticQualifierAutoLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  static function automatic void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(StaticMethodParsing, StaticFunctionDeclaration) {
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

TEST(StaticMethodParsing, StaticTaskDeclaration) {
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

TEST(StaticMethodParsing, StaticVirtualFunctionError) {
  auto r = Parse(
      "class C;\n"
      "  static virtual function int foo();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(StaticMethodParsing, StaticVirtualTaskError) {
  auto r = Parse(
      "class C;\n"
      "  virtual static task bar();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(StaticMethodParsing, StaticFlagPropagatedToMethod) {
  auto r = Parse(
      "class C;\n"
      "  static function void work();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_static);
  EXPECT_TRUE(m->method->is_static);
  EXPECT_FALSE(m->is_virtual);
}

TEST(StaticMethodParsing, StaticMethodWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  static function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_static);
  EXPECT_EQ(m->method->func_args.size(), 2u);
}

}  // namespace
