// §11.12: Let construct

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

TEST(Assertion, LetWithPastInBody) {
  SampledLetFixture f;
  // let get_past(x) = $past(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$past", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_past", body, {arg});
  f.ctx.RegisterLetDecl("get_past", decl);

  // Create variable sig = 42.
  auto* var = f.ctx.CreateVariable("sig", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 42);

  // get_past(sig) → let expansion → $past(x) with x=42 → stub returns 42.
  auto* call = SLMakeCall(f.arena, "get_past", {SLMakeId(f.arena, "sig")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
