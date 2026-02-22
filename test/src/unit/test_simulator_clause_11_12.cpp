// §11.12: Let construct

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <cstdint>
#include <gtest/gtest.h>

using namespace delta;

struct SampledLetFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *SLMakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr *SLMakeSysCall(Arena &arena, std::string_view callee,
                           std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static Expr *SLMakeCall(Arena &arena, std::string_view callee,
                        std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

static ModuleItem *SLMakeLetDecl(Arena &arena, std::string_view name,
                                 Expr *body,
                                 std::vector<FunctionArg> args = {}) {
  auto *item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}
namespace {

TEST(Assertion, LetWithPastInBody) {
  SampledLetFixture f;
  // let get_past(x) = $past(x);
  FunctionArg arg;
  arg.name = "x";
  auto *body = SLMakeSysCall(f.arena, "$past", {SLMakeId(f.arena, "x")});
  auto *decl = SLMakeLetDecl(f.arena, "get_past", body, {arg});
  f.ctx.RegisterLetDecl("get_past", decl);

  // Create variable sig = 42.
  auto *var = f.ctx.CreateVariable("sig", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 42);

  // get_past(sig) → let expansion → $past(x) with x=42 → stub returns 42.
  auto *call = SLMakeCall(f.arena, "get_past", {SLMakeId(f.arena, "sig")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Assertion, LetWithChangedInBody) {
  SampledLetFixture f;
  // let check_changed(x) = $changed(x);
  FunctionArg arg;
  arg.name = "x";
  auto *body = SLMakeSysCall(f.arena, "$changed", {SLMakeId(f.arena, "x")});
  auto *decl = SLMakeLetDecl(f.arena, "check_changed", body, {arg});
  f.ctx.RegisterLetDecl("check_changed", decl);

  auto *var = f.ctx.CreateVariable("sig2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);

  // check_changed(sig2) → let expansion → $changed(x) with x=5 → stub returns
  // 0.
  auto *call =
      SLMakeCall(f.arena, "check_changed", {SLMakeId(f.arena, "sig2")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Assertion, LetWithSampledInBody) {
  SampledLetFixture f;
  // let get_sampled(x) = $sampled(x);
  FunctionArg arg;
  arg.name = "x";
  auto *body = SLMakeSysCall(f.arena, "$sampled", {SLMakeId(f.arena, "x")});
  auto *decl = SLMakeLetDecl(f.arena, "get_sampled", body, {arg});
  f.ctx.RegisterLetDecl("get_sampled", decl);

  auto *var = f.ctx.CreateVariable("sig3", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  // get_sampled(sig3) → let expansion → $sampled(x) with x=99 → returns 99.
  auto *call = SLMakeCall(f.arena, "get_sampled", {SLMakeId(f.arena, "sig3")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

} // namespace
