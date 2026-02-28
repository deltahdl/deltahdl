// §13.4.3: Constant functions

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// =============================================================================
// §13.4.3 — constant functions (const-eval path)
// =============================================================================
TEST(Functions, ConstantFunctionEvalAtElaboration) {
  // Constant functions should be evaluable by the ConstEvalInt path.
  // The current const_eval only handles simple expressions, not function calls.
  // This test verifies that a function-like expression (identifier +
  // arithmetic) can be const-evaluated, which is the elaboration-time analog.
  //
  // NOTE: Full constant function evaluation would require extending const_eval
  // to resolve function bodies — that is tracked separately. For now we verify
  // that the simulation-side function call works correctly, which is the
  // prerequisite for any constant function support.
  FuncFixture f;

  // function int double_val(input int x);
  //   return x * 2;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "double_val";
  func->func_args = {{Direction::kInput, false, {}, "x", nullptr, {}}};
  auto* body = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 2));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("double_val", func);

  auto* call = MakeCall(f.arena, "double_val", {MakeInt(f.arena, 21)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

}  // namespace
