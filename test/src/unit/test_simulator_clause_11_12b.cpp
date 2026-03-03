// Non-LRM tests

#include <cstdint>
#include "fixture_simulator.h"
#include "simulator/assertion.h"
#include "simulator/eval.h"

using namespace delta;

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

namespace {

TEST(Assertion, LetWithSampledInBody) {
  SampledLetFixture f;
  // let get_sampled(x) = $sampled(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$sampled", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_sampled", body, {arg});
  f.ctx.RegisterLetDecl("get_sampled", decl);

  auto* var = f.ctx.CreateVariable("sig3", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  // get_sampled(sig3) → let expansion → $sampled(x) with x=99 → returns 99.
  auto* call = SLMakeCall(f.arena, "get_sampled", {SLMakeId(f.arena, "sig3")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

}  // namespace
