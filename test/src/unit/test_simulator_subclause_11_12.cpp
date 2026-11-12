#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

static ModuleItem* MakeLetDecl(Arena& arena, std::string_view name, Expr* body,
                               std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}

namespace {

TEST(LetExpansionSimulation, LetRecursionGuard) {
  SimFixture f;

  auto* body_call = MakeCall(f.arena, "bad", {[&]() {
                               auto* e = f.arena.Create<Expr>();
                               e->kind = ExprKind::kBinary;
                               e->op = TokenKind::kPlus;
                               e->lhs = MakeId(f.arena, "a");
                               e->rhs = MakeInt(f.arena, 1);
                               return e;
                             }()});
  FunctionArg arg;
  arg.name = "a";
  auto* decl = MakeLetDecl(f.arena, "bad", body_call, {arg});
  f.ctx.RegisterLetDecl("bad", decl);

  auto* call = MakeCall(f.arena, "bad", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_TRUE(result.nwords > 0);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "recursive instantiation of let 'bad' is not permitted", 0, "11.12"));
}

static Expr* SLMakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* SLMakeSysCall(Arena& arena, std::string_view callee,
                           std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static Expr* SLMakeCall(Arena& arena, std::string_view callee,
                        std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static ModuleItem* SLMakeLetDecl(Arena& arena, std::string_view name,
                                 Expr* body,
                                 std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}

TEST(LetExpansionSimulation, LetWithPastInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$past", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_past", body, {arg});
  f.ctx.RegisterLetDecl("get_past", decl);

  auto* var = f.ctx.CreateVariable("sig", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* call = SLMakeCall(f.arena, "get_past", {SLMakeId(f.arena, "sig")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, LetWithChangedInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$changed", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "check_changed", body, {arg});
  f.ctx.RegisterLetDecl("check_changed", decl);

  auto* var = f.ctx.CreateVariable("sig2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);

  auto* call =
      SLMakeCall(f.arena, "check_changed", {SLMakeId(f.arena, "sig2")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(LetExpansionSimulation, LetWithSampledInBody) {
  SampledLetFixture f;

  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$sampled", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_sampled", body, {arg});
  f.ctx.RegisterLetDecl("get_sampled", decl);

  auto* var = f.ctx.CreateVariable("sig3", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* call = SLMakeCall(f.arena, "get_sampled", {SLMakeId(f.arena, "sig3")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

TEST(LetExpansionSimulation, LetExpandMultipleArgs) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  FunctionArg arg_c;
  arg_c.name = "c";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kBinary;
  rhs->op = TokenKind::kPlus;
  rhs->lhs = MakeId(f.arena, "b");
  rhs->rhs = MakeId(f.arena, "c");
  body->rhs = rhs;
  auto* decl = MakeLetDecl(f.arena, "sum3", body, {arg_a, arg_b, arg_c});
  f.ctx.RegisterLetDecl("sum3", decl);

  auto* call = MakeCall(
      f.arena, "sum3",
      {MakeInt(f.arena, 10), MakeInt(f.arena, 20), MakeInt(f.arena, 30)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 60u);
}

TEST(LetExpansionSimulation, LetExpandAllDefaults) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  arg_a.default_value = MakeInt(f.arena, 7);
  FunctionArg arg_b;
  arg_b.name = "b";
  arg_b.default_value = MakeInt(f.arena, 3);
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "def_add", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("def_add", decl);

  auto* call = MakeCall(f.arena, "def_add", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetCallInInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = add(10, 20);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(LetExpansionSimulation, EndToEndLetNoArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let magic = 42;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = magic;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, EndToEndLetWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let inc(x, step = 1) = x + step;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = inc(10);\n"
      "    r2 = inc(10, 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 11u);
  EXPECT_EQ(v2->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndLetTernaryBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = max(3, 7);\n"
      "    r2 = max(10, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 7u);
  EXPECT_EQ(v2->value.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetMultipleDecls) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = add(10, 3);\n"
      "    r2 = sub(10, 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 13u);
  EXPECT_EQ(v2->value.ToUint64(), 7u);
}

TEST(LetExpansionSimulation, EndToEndLetNestedCalls) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let inc(x) = x + 1;\n"
      "  let dbl(x) = x * 2;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = dbl(inc(3));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(LetExpansionSimulation, EndToEndLetParenthesizedPrecedence) {
  SimFixture f;

  auto* design = ElaborateSrc(
      "module t;\n"
      "  let add(a, b) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = add(2, 3) * 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(LetExpansionSimulation, EndToEndTypedFormalCastsActualToFormalWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let low4(logic [3:0] x) = x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = low4(8'd255);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndUntypedFormalDoesNotCastActual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let pass(x) = x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = pass(8'd255);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 255u);
}

TEST(LetExpansionSimulation, EndToEndTwoStateFormalDrivesXZActualBitsToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let low(bit [7:0] x) = x;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    src = 8'b101010xz;\n"
      "    result = low(src);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA8u);
}

TEST(LetExpansionSimulation, LetDeclarativeScopeIgnoresInstantiationVar) {
  SimFixture f;

  MakeVar(f, "K", 32, 42);

  auto* body = MakeId(f.arena, "K");
  auto* decl = MakeLetDecl(f.arena, "get_k", body);
  f.ctx.RegisterLetDecl("get_k", decl);

  f.ctx.PushScope();
  auto* local_k = f.ctx.CreateLocalVariable("K", 32);
  local_k->value = MakeLogic4VecVal(f.arena, 32, 999);

  auto* call = MakeCall(f.arena, "get_k", {});
  auto result = EvalExpr(call, f.ctx, f.arena);

  f.ctx.PopScope();

  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(LetExpansionSimulation, EndToEndLetNamedArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let sub(a, b) = a - b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = sub(.b(3), .a(10));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LetExpansionSimulation, EndToEndLetMixedPositionalAndNamedArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a, b, c) = a + b + c;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f(1, .c(3), .b(2));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(LetExpansionSimulation, EndToEndLetNamedActualLeavesDefaultInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a, b = 10) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f(.a(5));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LetExpansionSimulation, EndToEndLetAllDefaultsCallOmitsAllActuals) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let f(a = 7, b = 3) = a + b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LetExpansionSimulation, EndToEndLetBodyWithSampledValueCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let get_sampled(x) = $sampled(x);\n"
      "  logic [31:0] sig;\n"
      "  int result;\n"
      "  initial begin\n"
      "    sig = 99;\n"
      "    result = get_sampled(sig);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(LetExpansionSimulation, EndToEndRecursiveLetInstantiationIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let r(x) = r(x) + 1;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = r(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive instantiation of let", 2, "11.12"));
}

TEST(LetExpansionSimulation, RecursiveInstantiationNames11_12) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let cyc(v) = cyc(v) - 1;\n"
      "  int result;\n"
      "  initial result = cyc(9);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive instantiation of let", 2, "11.12"));
}

TEST(LetExpansionSimulation, RecursiveInstantiationMessageHoldsNoSubclause) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  let cyc(v) = cyc(v) - 1;\n"
      "  int result;\n"
      "  initial result = cyc(9);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive instantiation of let", 2, "11.12"));
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("§"), std::string::npos);
  }
}

TEST(LetDeclarationSim, PackageLetThroughImportScopeAndMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "package pex;\n"
      "  let valid_arb(request, valid, override) =\n"
      "      |(request & valid) || override;\n"
      "  let twice(a) = a * 2;\n"
      "endpackage\n"
      "module t;\n"
      "  import pex::*;\n"
      "  logic [1:0] req = 2'b10, vld = 2'b10, vld2 = 2'b01;\n"
      "  logic ovr = 0;\n"
      "  class C;\n"
      "    int n = 7;\n"
      "    function int m(); return twice(n) + 1; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%0d %0d %0d %0d %0d\",\n"
      "             valid_arb(.request(req), .valid(vld), .override(ovr)),\n"
      "             valid_arb(req, vld2, ovr), pex::valid_arb(req, vld2, "
      "1'b1),\n"
      "             pex::twice(7), h.m());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1 14 15\n");
}

TEST(LetConstructSim, ATypedefNamedFormalCastsItsActual) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit [15:0] bits;\n"
      "  logic [15:0] a, b;\n"
      "  let ones_match(bits x, y) = x == y;\n"
      "  initial begin\n"
      "    a = 16'b11; b = 16'b1x;\n"
      "    $display(\"%b %b\", ones_match(a, b), ones_match(b, 16'b10));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

TEST(LetConstructSim, AnImplicitTypeOfASigningAloneCastsItsActual) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  let f(signed x) = x;\n"
      "  let g(signed x, y) = y;\n"
      "  let h(unsigned x) = x;\n"
      "  let p([3:0] x) = x;\n"
      "  initial $display(\"%0d %0d %0d %0d\", f(8'hFF), g(1'b0, 8'hFF),\n"
      "                   h(8'hFF), p(8'hFF));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-1 -1 1 15\n");
}

TEST(LetConstructSim, AnUntypedFormalTakesNoTypeWrittenBeforeIt) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  let h(signed x, untyped y) = y;\n"
      "  let k(signed x, y) = y;\n"
      "  let n(signed x, untyped y, z) = z;\n"
      "  initial $display(\"%0d %0d %0d\", h(1'b0, 8'hFF), k(1'b0, 8'hFF),\n"
      "                   n(1'b0, 1'b0, 8'hFF));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "255 -1 255\n");
}

TEST(LetConstructSim, ALetDeclaredInATaskIsUsedThere) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  task automatic show();\n"
      "    let plus(x, y = 4) = x + y;\n"
      "    $display(\"%0d %0d\", plus(7), plus(7, 1));\n"
      "  endtask\n"
      "  initial show();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "11 8\n");
}

TEST(LetConstructSim, ExampleBsLetReadsItsDeclarationScopesX) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  logic x = 1'b1;\n"
      "  logic a, b;\n"
      "  let y = x;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    begin\n"
      "      static bit x = 1'b0;\n"
      "      b = a | y;\n"
      "      $display(\"%0d\", b);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(LetSim, BlockLetsAreTheirScopesAndSeeTheirScopesNames) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  task automatic t1(); let p = 1; $display(\"%0d\", p);"
                 " endtask\n"
                 "  task automatic t2(); let p = 2; $display(\"%0d\", p);"
                 " endtask\n"
                 "  function automatic int f(int a);\n"
                 "    let dbl = a * 2;\n"
                 "    return dbl;\n"
                 "  endfunction\n"
                 "  initial begin t1(); t2(); $display(\"%0d\", f(3)); end\n"
                 "endmodule\n",
                 f),
      "1\n2\n6\n");
}

TEST(LetSim, ActualsAreSubstitutedWithTheirTypes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  int v = -5;\n"
                 "  logic [7:0] a = 8'hFF, b = 8'h01;\n"
                 "  logic [8:0] r;\n"
                 "  let add(x, y) = x + y;\n"
                 "  let neg(x) = x < 0;\n"
                 "  let w(int x) = $bits(x);\n"
                 "  let n(byte x) = x < 0;\n"
                 "  initial begin\n"
                 "    r = add(a, b);\n"
                 "    $display(\"%0d %0d %0d %0d %0d %h\", add(add(1, 2), 3),\n"
                 "             neg(v), w(8'hFF), n(8'hFF), n(8'h01), r);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "6 1 32 1 0 100\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(LetSim, DefaultsReadTheDeclaringScopeAndInstancesKeepTheirHistory) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic b = 1;\n"
                       "  let eq(x, y = b) = x == y;\n"
                       "  logic clk = 0, a = 0, c = 1, pa, pc;\n"
                       "  let prev(x) = $past(x);\n"
                       "  always #5 clk = ~clk;\n"
                       "  always @(posedge clk) begin\n"
                       "    pa = prev(a);\n"
                       "    pc = prev(c);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    automatic logic b = 0;\n"
                       "    $display(\"%0d\", eq(1'b1));\n"
                       "    #31 $display(\"%b %b\", pa, pc);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n0 1\n$finish at time 31\n");
}

TEST(LetSim, ReferencesReachTheInnermostVisibleLet) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("let p = 9;\n"
                 "let q = 7;\n"
                 "module child; let p = 2; initial $display(\"%0d\", p);"
                 " endmodule\n"
                 "module top;\n"
                 "  let p = 1;\n"
                 "  child u();\n"
                 "  initial begin\n"
                 "    #1 $display(\"%0d\", p);\n"
                 "    begin let p = 3; $display(\"%0d\", p); end\n"
                 "    $display(\"%0d %0d\", p, q);\n"
                 "  end\n"
                 "  initial #2 fork let w = 5; $display(\"%0d\", w); join\n"
                 "endmodule\n",
                 f),
      "2\n1\n3\n1 7\n5\n");
}

TEST(LetSim, ASubroutineBlocksLetEndsWithTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  let p = 1;\n"
                       "  function int f();\n"
                       "    int r;\n"
                       "    begin let p = 3; r = p; end\n"
                       "    return r * 10 + p;\n"
                       "  endfunction\n"
                       "  task t();\n"
                       "    begin let p = 4; $display(\"%0d\", p); end\n"
                       "    $display(\"%0d\", p);\n"
                       "  endtask\n"
                       "  initial begin $display(\"%0d\", f()); t(); end\n"
                       "endmodule\n",
                       f),
            "31\n4\n1\n");
}

TEST(LetSim, ACompilationUnitLetsTypeReferenceFormalCastsItsActual) {
  SimFixture f;
  EXPECT_EQ(RunCapture("byte b;\n"
                       "let g(type(b) y) = y;\n"
                       "module top;\n"
                       "  initial $display(\"%0d\", g(16'h1FF));\n"
                       "endmodule\n",
                       f),
            "-1\n");
}

TEST(LetExamplesSim, TheMultExampleSizesItsProductByItsOperandsBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  let mult(x, y) = ($bits(x) + $bits(y))'(x * y);\n"
          "  logic [3:0] a = 15;\n"
          "  logic [1:0] b = 3;\n"
          "  initial $display(\"%0d %0d\", mult(a, b), $bits(mult(a, b)));\n"
          "endmodule\n",
          f),
      "45 6\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LetExamplesSim, TheAtLeastTwoExampleAssertsWithAndWithoutItsDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  let at_least_two(sig, rst = 1'b0) = rst || ($countones(sig) >= "
          "2);\n"
          "  logic [15:0] sig1 = 16'h0101;\n"
          "  logic [3:0] sig2 = 4'b1110;\n"
          "  initial begin\n"
          "    #1;\n"
          "    q1: assert (at_least_two(sig1)) $display(\"q1 pass\");\n"
          "    else $display(\"q1 fail\");\n"
          "    q2: assert (at_least_two(~sig2)) $display(\"q2 pass\");\n"
          "    else $display(\"q2 fail\");\n"
          "    q3: assert (at_least_two(~sig2, 1)) $display(\"q3 pass\");\n"
          "    else $display(\"q3 fail\");\n"
          "  end\n"
          "endmodule\n",
          f),
      "q1 pass\nq2 fail\nq3 pass\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LetExamplesSim, AShortcutForAHierarchicalSubexpressionIsPassedToATask) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module u;\n"
                "  logic [31:0] base = 100, displ = 7;\n"
                "endmodule\n"
                "module b;\n"
                "  u unit1();\n"
                "  u unit2();\n"
                "endmodule\n"
                "module top;\n"
                "  b block1();\n"
                "  task write_value(input logic [31:0] ad, input logic [31:0] "
                "value);\n"
                "    $display(\"%0d %0d\", ad, value);\n"
                "  endtask\n"
                "  let addr = top.block1.unit1.base + top.block1.unit2.displ;\n"
                "  initial #1 write_value(addr, 0);\n"
                "endmodule\n",
                f),
            "107 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LetExamplesSim, TheFormalsAndTheDefaultOfTheEqExampleAreSubstituted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic clk = 0, a = 1, b = 1;\n"
                       "  logic p = 1, q = 0, r = 1;\n"
                       "  let eq(x, y = b) = x == y;\n"
                       "  let tmp = a && b;\n"
                       "  initial #5 clk = 1;\n"
                       "  a1: assert property (@(posedge clk) eq(p,q)) else "
                       "$display(\"a1 fail %0t\", $time);\n"
                       "  always_comb begin\n"
                       "    a2: assert (eq(r)) $display(\"a2 pass\");\n"
                       "    a3: assert (tmp) $display(\"a3 pass\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a2 pass\na3 pass\na1 fail 5\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LetExamplesSim, LetsOfAnInterfaceAProgramAndACheckerExpandThere) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I;\n"
                       "  int a = 4;\n"
                       "  let dbl(x) = x * 2;\n"
                       "  int r;\n"
                       "  initial #1 r = dbl(a);\n"
                       "endinterface\n"
                       "program p;\n"
                       "  int b = 5;\n"
                       "  let tri3(x) = x * 3;\n"
                       "  initial #4 $display(\"P %0d\", tri3(b));\n"
                       "endprogram\n"
                       "checker c(logic s, logic clk);\n"
                       "  let inv(x) = !x;\n"
                       "  a: assert property (@(posedge clk) inv(s))\n"
                       "    $display(\"C pass %0t\", $time);\n"
                       "  else $display(\"C fail %0t\", $time);\n"
                       "endchecker\n"
                       "module m;\n"
                       "  logic s = 0, clk = 0;\n"
                       "  I i();\n"
                       "  p pp();\n"
                       "  c ci(s, clk);\n"
                       "  initial begin\n"
                       "    #2 clk = 1;\n"
                       "    #1 $display(\"I %0d\", i.r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "C pass 2\nI 8\nP 15\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LetExamplesSim, DISABLED_ANameANestedScopeDeclaresHidesALetDeclaredLater) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int k = 1;\n"
                       "  task t(input int k2);\n"
                       "    int addr;\n"
                       "    addr = k2;\n"
                       "    $display(\"%0d\", addr);\n"
                       "  endtask\n"
                       "  function int f(int addr);\n"
                       "    return addr * 10;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    int addr;\n"
                       "    addr = 5;\n"
                       "    $display(\"%0d\", addr);\n"
                       "  end\n"
                       "  let addr = k + 1;\n"
                       "  initial #1 begin\n"
                       "    t(addr);\n"
                       "    $display(\"%0d\", f(addr));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n2\n20\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
