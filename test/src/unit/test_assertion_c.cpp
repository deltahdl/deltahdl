// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

TEST(Assertion, LetWithChangedInBody) {
  SampledLetFixture f;
  // let check_changed(x) = $changed(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$changed", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "check_changed", body, {arg});
  f.ctx.RegisterLetDecl("check_changed", decl);

  auto* var = f.ctx.CreateVariable("sig2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);

  // check_changed(sig2) → let expansion → $changed(x) with x=5 → stub returns
  // 0.
  auto* call =
      SLMakeCall(f.arena, "check_changed", {SLMakeId(f.arena, "sig2")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

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
