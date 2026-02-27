// §13.5: Subroutine calls and argument passing

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

TEST(Functions, VoidFunctionSideEffect) {
  FuncFixture f;

  // Global variable "g" that the function modifies via output arg.
  auto* g_var = f.ctx.CreateVariable("g", 32);
  g_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // function void store(output int out); out = 99; endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "store";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kOutput, false, {}, "out", nullptr, {}}};
  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "out", MakeInt(f.arena, 99)));
  f.ctx.RegisterFunction("store", func);

  auto* call = MakeCall(f.arena, "store", {MakeId(f.arena, "g")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(g_var->value.ToUint64(), 99u);
}

}  // namespace
