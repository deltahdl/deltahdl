// §11.12: Let construct

#include <cstring>

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

static Variable* MakeVar(SimFixture& f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

static ModuleItem* MakeLetDecl(Arena& arena, std::string_view name, Expr* body,
                               std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}
namespace {

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

TEST(EvalAdv, LetExpandDefaultArg) {
  SimFixture f;
  // let inc(a, b = 1) = a + b;
  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  arg_b.default_value = MakeInt(f.arena, 1);
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "inc", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("inc", decl);

  // inc(10) — uses default b=1, should return 11.
  auto* call = MakeCall(f.arena, "inc", {MakeInt(f.arena, 10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 11u);
}

TEST(EvalAdv, LetNoRecursive) {
  SimFixture f;
  // let bad(a) = bad(a + 1); — recursive, should return X (not infinite loop).
  auto* body_call = MakeCall(f.arena, "bad", {[&]() {
                               auto* e = f.arena.Create<Expr>();
                               e->kind = ExprKind::kBinary;
                               e->op = TokenKind::kPlus;
                               e->lhs = MakeId(f.arena, "a");
                               e->rhs = MakeInt(f.arena, 1);
                               return e;
                             }()});
  FunctionArg arg;
  arg.name = "a";
  auto* decl = MakeLetDecl(f.arena, "bad", body_call, {arg});
  f.ctx.RegisterLetDecl("bad", decl);

  auto* call = MakeCall(f.arena, "bad", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  // Should not infinite loop; returns X (bval != 0) or 0.
  EXPECT_TRUE(result.nwords > 0);
}

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
