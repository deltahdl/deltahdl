// §11.12: Let construct

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

}
TEST(EvalAdv, LetExpandSimple) {
  SimFixture f;
  // let add1(a) = a + 1;
  FunctionArg arg;
  arg.name = "a";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeInt(f.arena, 1);
  auto* decl = MakeLetDecl(f.arena, "add1", body, {arg});
  f.ctx.RegisterLetDecl("add1", decl);

  // add1(5) should return 6.
  auto* call = MakeCall(f.arena, "add1", {MakeInt(f.arena, 5)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

}  // namespace
