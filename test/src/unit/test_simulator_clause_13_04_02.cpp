// §13.4.2: Static and automatic functions

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

static ModuleItem* MakeCounterFunc(Arena& arena) {
  auto* func = arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  auto* rhs = MakeBinary(arena, TokenKind::kPlus, MakeId(arena, "counter"),
                         MakeInt(arena, 1));
  func->func_body_stmts.push_back(MakeAssign(arena, "counter", rhs));
  return func;
}

namespace {

// =============================================================================
// §13.3.1, §13.4.2 — static vs automatic lifetime
// =============================================================================
TEST(Functions, StaticFunctionPersistsVariables) {
  FuncFixture f;

  // function static int counter();
  //   counter = counter + 1;
  // endfunction
  auto* func = MakeCounterFunc(f.arena);
  func->is_static = true;
  func->is_automatic = false;
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

  // First call: counter starts at 0, returns 0+1=1
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  // Second call: counter is still 1 from last call, returns 1+1=2
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 2u);
  // Third call: counter is 2, returns 3
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 3u);
}

TEST(Functions, AutomaticFunctionFreshVariables) {
  FuncFixture f;

  // function automatic int counter();
  //   counter = counter + 1;
  // endfunction
  auto* func = MakeCounterFunc(f.arena);
  func->is_automatic = true;
  func->is_static = false;
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

  // Each call starts fresh: 0+1=1 every time.
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Functions, StaticFunctionWithArgs) {
  FuncFixture f;

  // function static int accum(input int v);
  //   accum = accum + v;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "accum";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "accum"),
                         MakeId(f.arena, "v"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "accum", rhs));
  f.ctx.RegisterFunction("accum", func);

  // accum(5) => 0 + 5 = 5
  auto* c1 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 5)});
  EXPECT_EQ(EvalExpr(c1, f.ctx, f.arena).ToUint64(), 5u);
  // accum(3) => 5 + 3 = 8
  auto* c2 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 3)});
  EXPECT_EQ(EvalExpr(c2, f.ctx, f.arena).ToUint64(), 8u);
  // accum(2) => 8 + 2 = 10
  auto* c3 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 2)});
  EXPECT_EQ(EvalExpr(c3, f.ctx, f.arena).ToUint64(), 10u);
}

}  // namespace
