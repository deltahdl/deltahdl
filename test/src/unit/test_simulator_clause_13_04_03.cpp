#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(Functions, ConstantFunctionEvalAtElaboration) {

  FuncFixture f;

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

}
