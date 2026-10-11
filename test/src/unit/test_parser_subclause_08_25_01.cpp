#include <gtest/gtest.h>

#include <map>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionParsing, ScopeCallParsesAsExpr) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] d;\n"
      "  logic [2:0] e;\n"
      "  assign e = Codec#(8)::encode(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, TwoSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a4;\n"
      "  logic [15:0] a16;\n"
      "  logic [1:0] r4;\n"
      "  logic [3:0] r16;\n"
      "  assign r4  = C#(4)::ENCODER_f(a4);\n"
      "  assign r16 = C#(16)::ENCODER_f(a16);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, MultiParamSpecialization) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [31:0] result;\n"
      "  assign result = Xform#(16, 32, 2)::widen(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, TypeParamOverrideCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  assign y = Converter#(logic [7:0])::identity(x);\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ChainedParameterizedCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a, b, c;\n"
              "  assign c = Arith#(8)::add(a, Arith#(8)::add(a, b));\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, CallParamTaskFromInitial) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial Utils#(16)::report();\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ParamCallInTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  logic sel;\n"
              "  assign y = sel ? C#(8)::ENCODER_f(x) : '0;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ExplicitDefaultAccessesLocalParam) {
  auto r = Parse(
      "module m;\n"
      "  class par_cls #(parameter int a = 25);\n"
      "    parameter int b = 23;\n"
      "  endclass\n"
      "  initial begin\n"
      "    $display(par_cls#()::b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParameterizedScopeResolutionParsing, ExplicitSpecAccessesClassParam) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class C #(parameter int p = 1);\n"
              "  endclass\n"
              "  int result;\n"
              "  initial result = C#(5)::p;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing,
     OutOfBlockMethodForParameterizedClass) {
  EXPECT_TRUE(
      ParseOk("class C #(int p = 1);\n"
              "  extern static function int f();\n"
              "endclass\n"
              "function int C::f();\n"
              "  return p;\n"
              "endfunction\n"
              "module m;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, EmptyParamListWithMemberAccess) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class C #(parameter int p = 10);\n"
              "    parameter int q = 20;\n"
              "  endclass\n"
              "  int a, b;\n"
              "  initial begin\n"
              "    a = C#()::p;\n"
              "    b = C#()::q;\n"
              "  end\n"
              "endmodule\n"));
}

// A.4.1.1's ordered_parameter_assignment is a param_expression (printed page
// 1194 of IEEE 1800-2023), which A.8.3 lets be a data_type, and A.2.2.1
// gives an integer type an optional signing and a virtual interface its
// `virtual` keyword (printed page 1182). An expression reader spells a keyword
// type as a bare name, so `int unsigned` stopped at `unsigned` and `virtual
// ifc` at `virtual`, each reported as a missing `)` under §23.10.2; those
// elements are now read as the data types they are and carried on the scope's
// node.
TEST(ParameterizedScopeResolutionParsing, SignedIntegerTypeAsParameterValue) {
  auto r = Parse(
      "class C #(type T = int);\n"
      "  static function T get();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = C#(int unsigned)::get();\n"
      "  initial void'(C#(byte signed)::get());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* call = stmt->rhs;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->kind, ExprKind::kCall);
  auto* scope = call->lhs->lhs;
  ASSERT_NE(scope, nullptr);
  EXPECT_TRUE(scope->has_param_spec);
  ASSERT_EQ(scope->elements.size(), 1u);
  ASSERT_NE(scope->elements[0], nullptr);
  ASSERT_EQ(scope->elements[0]->kind, ExprKind::kTypeRef);
  ASSERT_NE(scope->elements[0]->type_value, nullptr);
  EXPECT_EQ(scope->elements[0]->type_value->kind, DataTypeKind::kInt);
  EXPECT_FALSE(scope->elements[0]->type_value->is_signed);
}

TEST(ParameterizedScopeResolutionParsing,
     VirtualInterfaceTypeAsParameterValue) {
  auto r = Parse(
      "interface ifc;\n"
      "endinterface\n"
      "class C #(type T = int);\n"
      "  static function void set(int v);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial C#(virtual ifc)::set(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kExprStmt);
  auto* scope = stmt->expr->lhs->lhs;
  ASSERT_NE(scope, nullptr);
  ASSERT_EQ(scope->elements.size(), 1u);
  ASSERT_EQ(scope->elements[0]->kind, ExprKind::kTypeRef);
  ASSERT_NE(scope->elements[0]->type_value, nullptr);
  EXPECT_EQ(scope->elements[0]->type_value->kind,
            DataTypeKind::kVirtualInterface);
  EXPECT_EQ(scope->elements[0]->type_value->type_name, "ifc");
}

// A keyword type with no signing keeps the shape it had, a name the
// elaborator reads as the type, so `logic [3:0]` still arrives as a select
// on the name `logic`.
TEST(ParameterizedScopeResolutionParsing, PlainKeywordTypeStaysAName) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial x = C#(logic [3:0])::get();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* scope = stmt->rhs->lhs->lhs;
  ASSERT_NE(scope, nullptr);
  ASSERT_EQ(scope->elements.size(), 1u);
  ASSERT_EQ(scope->elements[0]->kind, ExprKind::kSelect);
  EXPECT_EQ(scope->elements[0]->base->kind, ExprKind::kIdentifier);
  EXPECT_EQ(scope->elements[0]->base->text, "logic");
}

// §8.25.1 tells C::T from C#()::T outside C, and both leave type_params
// empty, so a declared type records whether the class it was written behind
// was given a parameter_value_assignment, empty or not, on each path that
// parses one: a module's declaration through the class or through its
// package, and a declaration in a block.
TEST(ParameterizedScopeResolutionParsing, ScopeAssignmentIsRecordedOnTheType) {
  auto r = Parse(
      "package p; class C #(int n = 1); typedef int T; endclass endpackage\n"
      "class C #(int n = 1); typedef int T; endclass\n"
      "module m;\n"
      "  C::T a;\n"
      "  C#()::T b;\n"
      "  C#(3)::T c;\n"
      "  p::C::T d;\n"
      "  p::C#()::T e;\n"
      "  initial begin C::T f; C#()::T g; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::map<std::string_view, const DataType*> types;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      types[item->name] = &item->data_type;
    }
  }
  const Stmt* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  for (const Stmt* s : body->stmts) {
    if (s->kind == StmtKind::kVarDecl) types[s->var_name] = &s->var_decl_type;
  }
  const std::map<std::string_view, bool> kWritten = {
      {"a", false}, {"b", true},  {"c", true}, {"d", false},
      {"e", true},  {"f", false}, {"g", true}};
  for (const auto& [name, written] : kWritten) {
    ASSERT_TRUE(types.contains(name)) << name;
    EXPECT_EQ(types[name]->scope_name, "C") << name;
    EXPECT_EQ(types[name]->type_name, "T") << name;
    EXPECT_EQ(types[name]->scope_param_assignment_written, written) << name;
  }
}

}  // namespace
