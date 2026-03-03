// §8.6: Object methods

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 — method_call
// =============================================================================
// method_call: method_call_root . method_call_body (no args)
TEST(ParserA609, MethodCallNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

// =============================================================================
// A.8.2 Subroutine calls — method_call
// =============================================================================
// § method_call ::= method_call_root . method_call_body
// § method_call_root ::= primary | implicit_class_handle
// Basic method call on identifier
TEST(ParserA82, MethodCallBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
  ASSERT_NE(expr->lhs, nullptr);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kMemberAccess);
}

TEST(Parser, ClassWithMethod) {
  auto r = Parse(
      "class pkt;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_NE(cls->members[0]->method, nullptr);
}

// class_method ::= { method_qualifier } function_declaration
//                | { method_qualifier } task_declaration
TEST(SourceText, ClassMethods) {
  auto r = Parse(
      "class C;\n"
      "  function void foo(); endfunction\n"
      "  task bar(); endtask\n"
      "  static function int sfn(); endfunction\n"
      "  virtual task vtask(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "foo");
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->method->name, "bar");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_virtual);
}

// 13. Class with methods sharing scope with member variables
TEST(ParserClause03, Cl3_13_ClassMethodsAndProperties) {
  auto r = Parse(
      "class my_cls;\n"
      "  int count;\n"
      "  function void increment();\n"
      "    count = count + 1;\n"
      "  endfunction\n"
      "  task reset();\n"
      "    count = 0;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "count");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[1]->method, nullptr);
  EXPECT_EQ(cls->members[1]->method->name, "increment");
  EXPECT_EQ(cls->members[2]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[2]->method, nullptr);
  EXPECT_EQ(cls->members[2]->method->name, "reset");
}

}  // namespace
