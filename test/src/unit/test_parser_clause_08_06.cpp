#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

static ClassMember* FindMethodMember(ClassDecl* cls) {
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      return m;
    }
  }
  return nullptr;
}

TEST(ParserSection8, ClassWithTask) {
  auto r = Parse(
      "class MyClass;\n"
      "  task do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->kind, ModuleItemKind::kTaskDecl);
}

// §8.6: Method call via dot notation parses correctly.
TEST(ParserA86, MethodCallDotNotation) {
  auto r = Parse(
      "class Packet;\n"
      "  function int current_status();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int status;\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    status = p.current_status();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §8.6: Automatic lifetime on class method is legal (default).
TEST(ParserA86, MethodAutomaticLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  function automatic void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

// §8.6: No explicit lifetime on class method is legal (implicit automatic).
TEST(ParserA86, MethodNoLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  function void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

// §8.6: Static lifetime on class function is illegal.
TEST(ParserA86, FunctionStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  function static void foo();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// §8.6: Static lifetime on class task is illegal.
TEST(ParserA86, TaskStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// §8.6: Static class qualifier (static method) is NOT the same as static
// lifetime and is legal.
TEST(ParserA86, StaticClassQualifierLegal) {
  ParseOk(
      "class C;\n"
      "  static function void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

// §8.6: Method with both static qualifier and automatic lifetime is legal.
TEST(ParserA86, StaticQualifierAutoLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  static function automatic void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

}  // namespace
