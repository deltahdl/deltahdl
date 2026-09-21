#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
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

}  // namespace
