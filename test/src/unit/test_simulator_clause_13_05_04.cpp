// §13.5.4: Argument binding by name

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

// =============================================================================
// Test fixture shared by all function call tests
// =============================================================================
struct FuncFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: make an integer literal expression.
static Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: make an identifier expression.
static Expr *MakeIdent(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: make a binary expression.
static Expr *MakeBinary(Arena &arena, TokenKind op, Expr *lhs, Expr *rhs) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

// Helper: make a blocking assignment statement.
static Stmt *MakeAssign(Arena &arena, std::string_view lhs_name, Expr *rhs) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = rhs;
  return s;
}

// Helper: make a return statement.
static Stmt *MakeReturn(Arena &arena, Expr *expr) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

// Helper: make a function call with named arguments.
static Expr *MakeNamedCall(Arena &arena, std::string_view callee,
                           std::vector<Expr *> args,
                           std::vector<std::string_view> names) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  e->arg_names = std::move(names);
  return e;
}

namespace {

// =============================================================================
// §13.5.4 — named argument binding
// =============================================================================
TEST(Functions, NamedArguments) {
  FuncFixture f;

  // function int sub(input int x, input int y);
  //   return x - y;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "sub";
  func->func_args = {
      {Direction::kInput, false, {}, "x", nullptr, {}},
      {Direction::kInput, false, {}, "y", nullptr, {}},
  };
  auto *body_expr =
      MakeBinary(f.arena, TokenKind::kMinus, MakeIdent(f.arena, "x"),
                 MakeIdent(f.arena, "y"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("sub", func);

  // Call with named args in reversed order: sub(.y(3), .x(10)) => 10 - 3 = 7
  auto *call = MakeNamedCall(f.arena, "sub",
                             {MakeIntLit(f.arena, 3), MakeIntLit(f.arena, 10)},
                             {"y", "x"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 7u);
}

TEST(Functions, NamedArgsWithDefaults) {
  FuncFixture f;

  // function int weighted(input int a, input int w = 2);
  //   return a * w;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "weighted";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, {}, "w", MakeIntLit(f.arena, 2), {}},
  };
  auto *body_expr =
      MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "a"),
                 MakeIdent(f.arena, "w"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("weighted", func);

  // Named call providing only "a", defaulting "w" => 7 * 2 = 14
  auto *call =
      MakeNamedCall(f.arena, "weighted", {MakeIntLit(f.arena, 7)}, {"a"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 14u);
}

// =============================================================================
// Combined feature tests
// =============================================================================
TEST(Functions, NamedArgsReorderedWithRef) {
  FuncFixture f;

  auto *x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 100);

  // function void swap_add(ref int target, input int amount);
  //   target = target + amount;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "swap_add";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, {}, "target", nullptr, {}},
      {Direction::kInput, false, {}, "amount", nullptr, {}},
  };
  auto *rhs =
      MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "target"),
                 MakeIdent(f.arena, "amount"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "target", rhs));
  f.ctx.RegisterFunction("swap_add", func);

  // Call with named args in reversed order:
  // swap_add(.amount(5), .target(x))
  auto *call = MakeNamedCall(f.arena, "swap_add",
                             {MakeIntLit(f.arena, 5), MakeIdent(f.arena, "x")},
                             {"amount", "target"});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 105u);
}

TEST(Functions, DefaultsAndNamedArgsCombined) {
  FuncFixture f;

  // function int scale(input int val, input int factor = 3);
  //   return val * factor;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "scale";
  func->func_args = {
      {Direction::kInput, false, {}, "val", nullptr, {}},
      {Direction::kInput, false, {}, "factor", MakeIntLit(f.arena, 3), {}},
  };
  auto *body = MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "val"),
                          MakeIdent(f.arena, "factor"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("scale", func);

  // Named call with only "val", defaulting "factor":
  // scale(.val(7)) => 7 * 3 = 21
  auto *call =
      MakeNamedCall(f.arena, "scale", {MakeIntLit(f.arena, 7)}, {"val"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 21u);
}

} // namespace
