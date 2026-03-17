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

}  // namespace
