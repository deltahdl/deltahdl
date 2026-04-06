#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
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

TEST(LetExpansionSimulation, LetExpandSimple) {
  SimFixture f;

  FunctionArg arg;
  arg.name = "a";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeInt(f.arena, 1);
  auto* decl = MakeLetDecl(f.arena, "add1", body, {arg});
  f.ctx.RegisterLetDecl("add1", decl);

  auto* call = MakeCall(f.arena, "add1", {MakeInt(f.arena, 5)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

TEST(LetExpansionSimulation, LetExpandDefaultArg) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  arg_b.default_value = MakeInt(f.arena, 1);
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "inc", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("inc", decl);

  auto* call = MakeCall(f.arena, "inc", {MakeInt(f.arena, 10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 11u);
}

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
}

TEST(LetExpansionSimulation, LetDeclarativeScope) {
  SimFixture f;

  MakeVar(f, "K", 32, 42);
  auto* body = MakeId(f.arena, "K");
  auto* decl = MakeLetDecl(f.arena, "get_k", body);
  f.ctx.RegisterLetDecl("get_k", decl);

  auto* call = MakeCall(f.arena, "get_k", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
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
  auto* decl =
      MakeLetDecl(f.arena, "sum3", body, {arg_a, arg_b, arg_c});
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

TEST(LetExpansionSimulation, LetExpandOverridesDefault) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  arg_a.default_value = MakeInt(f.arena, 100);
  auto* body = MakeId(f.arena, "a");
  auto* decl = MakeLetDecl(f.arena, "get_a", body, {arg_a});
  f.ctx.RegisterLetDecl("get_a", decl);

  auto* call = MakeCall(f.arena, "get_a", {MakeInt(f.arena, 55)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 55u);
}

// --- End-to-end simulation tests ---

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
  // The expansion of `add(2, 3)` is parenthesized as `(2 + 3)`,
  // so `add(2, 3) * 4` evaluates as `(2 + 3) * 4 = 20`,
  // not `2 + 3 * 4 = 14`.
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

// --- Unit-level: named argument binding ---

TEST(LetExpansionSimulation, LetExpandNamedArgs) {
  SimFixture f;

  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kMinus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "diff", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("diff", decl);

  // Call with named args: diff(.b(3), .a(10)) => 10 - 3 = 7
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "diff";
  call->args = {MakeInt(f.arena, 3), MakeInt(f.arena, 10)};
  call->arg_names = {"b", "a"};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// --- Unit-level: declarative scope negative test ---

TEST(LetExpansionSimulation, LetDeclarativeScopeIgnoresInstantiationVar) {
  SimFixture f;

  // Create variable 'K' = 42 in module scope (declaration context).
  MakeVar(f, "K", 32, 42);

  // let body references 'K'.
  auto* body = MakeId(f.arena, "K");
  auto* decl = MakeLetDecl(f.arena, "get_k", body);
  f.ctx.RegisterLetDecl("get_k", decl);

  // Push a new scope (simulating entering a block) and create a shadowing 'K'.
  f.ctx.PushScope();
  auto* local_k = f.ctx.CreateLocalVariable("K", 32);
  local_k->value = MakeLogic4VecVal(f.arena, 32, 999);

  // The let body should resolve 'K' from the declaration scope (42),
  // not the instantiation scope (999).
  auto* call = MakeCall(f.arena, "get_k", {});
  auto result = EvalExpr(call, f.ctx, f.arena);

  f.ctx.PopScope();

  // §11.12: Free variables resolve from the declaration scope (42),
  // not the instantiation scope (999).
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
