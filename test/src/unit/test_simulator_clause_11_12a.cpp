// Non-LRM tests

#include <cstring>
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

static ModuleItem* MakeLetDecl(Arena& arena, std::string_view name, Expr* body,
                               std::vector<FunctionArg> args = {}) {

  auto* item = arena.Create<ModuleItem>();

  item->kind = ModuleItemKind::kLetDecl;

  item->name = name;

  item->init_expr = body;

  item->func_args = std::move(args);

  return item;

namespace {

TEST(EvalAdv, LetDeclarativeScope) {
  SimFixture f;
  // let get_k() = K;
  // K is set in the outer scope before let registration.
  MakeVar(f, "K", 32, 42);
  auto* body = MakeId(f.arena, "K");
  auto* decl = MakeLetDecl(f.arena, "get_k", body);
  f.ctx.RegisterLetDecl("get_k", decl);

  // get_k() should access K=42 from declaration scope.
  auto* call = MakeCall(f.arena, "get_k", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
