#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

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

TEST(ThisParsing, ThisInClassTask) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "  task set_x(int x);\n"
              "    this.x = x;\n"
              "  endtask\n"
              "endclass\n"));
}

TEST(ThisParsing, ThisMemberAccessProducesAst) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function int get_x();\n"
      "    return this.x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  auto* method = cls->members[1]->method;
  ASSERT_GE(method->func_body_stmts.size(), 1u);
  auto* ret_stmt = method->func_body_stmts[0];
  ASSERT_NE(ret_stmt->expr, nullptr);
  EXPECT_EQ(ret_stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(ThisParsing, BareThisProducesIdentifier) {
  auto r = Parse(
      "class C;\n"
      "  function C get_self();\n"
      "    return this;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  auto* method = cls->members[0]->method;
  ASSERT_GE(method->func_body_stmts.size(), 1u);
  auto* ret_stmt = method->func_body_stmts[0];
  ASSERT_NE(ret_stmt->expr, nullptr);
  EXPECT_EQ(ret_stmt->expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ret_stmt->expr->text, "this");
}

TEST(ThisParsing, ThisWithMethodCall) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function void foo();\n"
              "  endfunction\n"
              "  function void bar();\n"
              "    this.foo();\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ThisParsing, ThisMultipleMemberAccesses) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int a;\n"
              "  int b;\n"
              "  function void swap(int a, int b);\n"
              "    this.a = b;\n"
              "    this.b = a;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §8.11 makes `this` a handle to the object the method runs in (printed page
// 187 of IEEE 1800-2023), and a name reached through it takes the same
// postfix chain as any other name: A.8.4's method_call and A.8.6's select run
// on, so `this.m[k].kill()` calls a method of a selected element. The parser
// read one call and one select after the `this.` chain and stopped, so the `.`
// before kill was reported as a missing ';' under §12.3.
TEST(ThisParsing, ThisSelectedElementMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  process m[int];\n"
      "  function void f(int k);\n"
      "    this.m[k].kill();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[1]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_body_stmts.size(), 1u);
  auto* stmt = method->func_body_stmts[0];
  ASSERT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  ASSERT_EQ(stmt->expr->kind, ExprKind::kCall);
  auto* callee = stmt->expr->lhs;
  ASSERT_NE(callee, nullptr);
  ASSERT_EQ(callee->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(callee->rhs->text, "kill");
  ASSERT_NE(callee->lhs, nullptr);
  EXPECT_EQ(callee->lhs->kind, ExprKind::kSelect);
}

TEST(ThisParsing, ThisSelectedElementMemberAndNestedSelect) {
  auto r = Parse(
      "class F;\n"
      "  int f;\n"
      "endclass\n"
      "class C;\n"
      "  F a[4];\n"
      "  int b[4][4];\n"
      "  function int g(int i, int j);\n"
      "    int x;\n"
      "    x = this.a[i].f;\n"
      "    x = this.b[i][j];\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[1]->members[2]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_body_stmts.size(), 4u);
  EXPECT_EQ(method->func_body_stmts[1]->kind, StmtKind::kBlockingAssign);
  auto* member = method->func_body_stmts[1]->rhs;
  ASSERT_NE(member, nullptr);
  ASSERT_EQ(member->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(member->rhs->text, "f");
  EXPECT_EQ(member->lhs->kind, ExprKind::kSelect);
  auto* nested = method->func_body_stmts[2]->rhs;
  ASSERT_NE(nested, nullptr);
  ASSERT_EQ(nested->kind, ExprKind::kSelect);
  EXPECT_EQ(nested->base->kind, ExprKind::kSelect);
}

TEST(ThisParsing, ThisCallResultMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  function C f();\n"
      "    return this;\n"
      "  endfunction\n"
      "  function void g();\n"
      "    this.f().g();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[1]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_body_stmts.size(), 1u);
  auto* call = method->func_body_stmts[0]->expr;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->kind, ExprKind::kCall);
  ASSERT_EQ(call->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(call->lhs->rhs->text, "g");
  EXPECT_EQ(call->lhs->lhs->kind, ExprKind::kCall);
}

}  // namespace
