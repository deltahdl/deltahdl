#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(ClassScopeResolutionParsing, TypedefAccess) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, StaticMethodCall) {
  auto r = Parse(
      "class Base;\n"
      "  static function void display();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial Base::display();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassScopeResolutionParsing, EnumMemberAccess) {
  auto r = Parse(
      "class Base;\n"
      "  typedef enum {bin, oct, dec, hex} radix;\n"
      "endclass\n"
      "module m;\n"
      "  initial x = Base::bin;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassScopeResolutionParsing, ParameterAccess) {
  auto r = Parse(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  logic [Cfg::WIDTH-1:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ClassScopeResolutionParsing, ChainedClassScope) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    static int x;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  initial y = Outer::Inner::x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, SuperclassScopeAccess) {
  auto r = Parse(
      "class Base;\n"
      "  static int count;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int get_count();\n"
      "    return Base::count;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, StaticPropertyRead) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  static int count;\n"
              "endclass\n"
              "module m;\n"
              "  int x;\n"
              "  initial x = C::count;\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, StaticPropertyWrite) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  static int count;\n"
              "endclass\n"
              "module m;\n"
              "  initial C::count = 5;\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, ScopeAsTypePrefix) {
  auto r = Parse(
      "class StringList;\n"
      "  class Node;\n"
      "    string name;\n"
      "  endclass\n"
      "endclass\n"
      "class StringTree;\n"
      "  class Node;\n"
      "    string name;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  StringList::Node n1;\n"
      "  StringTree::Node n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassScopeResolutionParsing, StaticTaskCall) {
  EXPECT_TRUE(
      ParseOk("class Logger;\n"
              "  static task log(string msg);\n"
              "  endtask\n"
              "endclass\n"
              "module m;\n"
              "  initial Logger::log(\"hello\");\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, DisambiguatesLocalFromClassMember) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  typedef enum {bin, oct, dec, hex} radix;\n"
              "  static task print(radix r, integer n);\n"
              "  endtask\n"
              "endclass\n"
              "module m;\n"
              "  int bin = 123;\n"
              "  initial Base::print(Base::bin, bin);\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, LocalparamAccess) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  localparam int SIZE = 16;\n"
              "endclass\n"
              "module m;\n"
              "  logic [C::SIZE-1:0] data;\n"
              "endmodule\n"));
}

TEST(ClassScopeResolutionParsing, NestedClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(r.cu->classes[0]->members[0]->nested_class->name, "Inner");
}

// A.2.2.1's class_type (printed page 1183 of the LRM) lets a
// parameter_value_assignment follow the class identifier before each `::`, and
// §8.25.1 (printed page 205) has a use of the scope resolution operator outside
// a parameterized class name its specialization, `C#(bit)::set(1)`. The block
// item predicate walked the `::` path of a known type name without reading the
// `#(...)`, so it stopped at `#`, took the line for a declaration, and
// ParseNamedType then met the call's `(` where a variable name should stand
// and reported it under §6.8.

// The one statement of module m's function f, read from a parse that reported
// nothing, is an expression statement holding a call: the shape a scoped call
// written as a statement takes, where a declaration would be a kVarDecl.
void ExpectSoleStatementOfFIsACall(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* f = FindItemByName(r.cu->modules[0]->items, "f");
  ASSERT_NE(f, nullptr);
  ASSERT_EQ(f->func_body_stmts.size(), 1u);
  EXPECT_EQ(f->func_body_stmts[0]->kind, StmtKind::kExprStmt);
  ASSERT_NE(f->func_body_stmts[0]->expr, nullptr);
  EXPECT_EQ(f->func_body_stmts[0]->expr->kind, ExprKind::kCall);
}

TEST(ClassScopeResolutionParsing,
     ParameterizedScopedCallInFunctionBodyIsAStatement) {
  auto r = Parse(
      "class C #(type T = int);\n"
      "  static function void set(int v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function void f();\n"
      "    C#(bit)::set(1);\n"
      "  endfunction\n"
      "endmodule\n");
  ExpectSoleStatementOfFIsACall(r);
}

TEST(ClassScopeResolutionParsing,
     ParameterizedScopedCallInInitialBlockIsAStatement) {
  auto r = Parse(
      "class C #(type T = int);\n"
      "  static function void set(int v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C#(bit)::set(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init = FirstItem(r, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  ASSERT_EQ(init->body->kind, StmtKind::kBlock);
  ASSERT_EQ(init->body->stmts.size(), 1u);
  EXPECT_EQ(init->body->stmts[0]->kind, StmtKind::kExprStmt);
  ASSERT_NE(init->body->stmts[0]->expr, nullptr);
  EXPECT_EQ(init->body->stmts[0]->expr->kind, ExprKind::kCall);
}

TEST(ClassScopeResolutionParsing,
     ForwardTypedefParameterizedScopedCallIsAStatement) {
  auto r = Parse(
      "typedef class D;\n"
      "class D #(int W = 4);\n"
      "  static function void set(int v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function void f();\n"
      "    D#(8)::set(3);\n"
      "  endfunction\n"
      "endmodule\n");
  ExpectSoleStatementOfFIsACall(r);
}

TEST(ClassScopeResolutionParsing,
     ParameterizedSpecializationStillDeclaresAVariable) {
  auto r = Parse(
      "class C #(type T = int);\n"
      "  static function void set(int v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function void f();\n"
      "    C#(bit) v;\n"
      "    C#(bit)::set(1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* f = FindItemByName(r.cu->modules[0]->items, "f");
  ASSERT_NE(f, nullptr);
  ASSERT_EQ(f->func_body_stmts.size(), 2u);
  EXPECT_EQ(f->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(f->func_body_stmts[0]->var_name, "v");
  EXPECT_EQ(f->func_body_stmts[1]->kind, StmtKind::kExprStmt);
}

}  // namespace
