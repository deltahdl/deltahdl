#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(ClassConstructorParsing, BlockingAssignment_ClassNew) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ClassConstructorParsing, BlockingAssignment_ClassNewWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(1, 2); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ClassConstructorParsing, DeclarationNewWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int a, int b);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, ConstructorStaticError) {
  auto r = Parse(
      "class C;\n"
      "  static function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "constructor shall not be declared static",
                            2, "8.7"));
}

TEST(ClassConstructorParsing, ConstructorVirtualError) {
  auto r = Parse(
      "class C;\n"
      "  virtual function new();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "constructor shall not be declared virtual", 2, "8.7"));
}

TEST(ClassConstructorParsing, ConstructorNoReturnType) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  auto* method = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(method->name, "new");
}

TEST(ClassConstructorParsing, ConstructorWithDefaultArgs) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  bit [12:0] address;\n"
      "  int cmd_time;\n"
      "  function new(int cmd = 0, bit [12:0] adrs = 0, int t = 0);\n"
      "    command = cmd;\n"
      "    address = adrs;\n"
      "    cmd_time = t;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, ConstructorEndlabelNew) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, PropertyWithExplicitDefault) {
  auto r = Parse(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  int c3 = 1;\n"
      "  function new(int a);\n"
      "    c2 = 2;\n"
      "    c3 = a;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, DerivedClassWithPropertyDefaults) {
  auto r = Parse(
      "class C;\n"
      "  int c1 = 1;\n"
      "  function new(int a);\n"
      "    c1 = a;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  int d1 = 4;\n"
      "  function new;\n"
      "    super.new(d1);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassConstructorParsing, DeclarationClassNewNoArgs) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A.2.4 spells class_new `[ class_scope ] new [ ( list_of_arguments ) ]`, and
// A.8.2 gives list_of_arguments a form that is named from its first element
// and a form that is ordered and then named. The three tests below read a
// `new` call of each form, and the fourth one whose named argument carries no
// value, which A.8.2 allows as `. identifier ( )`.
TEST(ClassConstructorParsing, NewCallNamedFromTheFirstArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(.orig_type(t), .full_inst_path(p)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->text, "new");
  ASSERT_EQ(stmt->rhs->arg_names.size(), 2u);
  EXPECT_EQ(stmt->rhs->arg_names[0], "orig_type");
  EXPECT_EQ(stmt->rhs->arg_names[1], "full_inst_path");
  ASSERT_EQ(stmt->rhs->args.size(), 2u);
  ASSERT_NE(stmt->rhs->args[0], nullptr);
  EXPECT_EQ(stmt->rhs->args[0]->text, "t");
  ASSERT_NE(stmt->rhs->args[1], nullptr);
  EXPECT_EQ(stmt->rhs->args[1]->text, "p");
}

TEST(ClassConstructorParsing, NewCallOrderedThenNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(1, 2, .c(3)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->args.size(), 3u);
  ASSERT_EQ(stmt->rhs->arg_names.size(), 1u);
  EXPECT_EQ(stmt->rhs->arg_names[0], "c");
}

TEST(ClassConstructorParsing, NewCallNamedArgumentWithoutAValue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(.a(), .b(1)); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  ASSERT_EQ(stmt->rhs->arg_names.size(), 2u);
  ASSERT_EQ(stmt->rhs->args.size(), 2u);
  EXPECT_EQ(stmt->rhs->args[0], nullptr);
  ASSERT_NE(stmt->rhs->args[1], nullptr);
}

TEST(ClassConstructorParsing, DeclarationNewCallNamedArguments) {
  auto r = Parse(
      "class C;\n"
      "  function new(int a, int b);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(.b(2), .a(1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
