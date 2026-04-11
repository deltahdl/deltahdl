#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ConstantFunctionSim, EvalAtElaboration) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "double_val";
  func->func_args = {{Direction::kInput, false, false, false, {}, "x", nullptr, {}}};
  auto* body = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 2));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("double_val", func);

  auto* call = MakeCall(f.arena, "double_val", {MakeInt(f.arena, 21)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

TEST(ConstantFunctionSim, NoArgFunction) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "forty_two";
  func->func_body_stmts.push_back(MakeReturn(f.arena, MakeInt(f.arena, 42)));
  f.ctx.RegisterFunction("forty_two", func);

  auto* call = MakeCall(f.arena, "forty_two", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

TEST(ConstantFunctionSim, MultipleArgFunction) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  func->func_args = {{Direction::kInput, false, false, false, {}, "a", nullptr, {}},
                     {Direction::kInput, false, false, false, {}, "b", nullptr, {}}};
  auto* body = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("add", func);

  auto* call =
      MakeCall(f.arena, "add", {MakeInt(f.arena, 10), MakeInt(f.arena, 32)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

}  // namespace
