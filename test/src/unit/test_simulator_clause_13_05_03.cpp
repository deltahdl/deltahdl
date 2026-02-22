// §13.5.3: Default argument values

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

// Helper: make a return statement.
static Stmt *MakeReturn(Arena &arena, Expr *expr) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

// Helper: make a function call expression.
static Expr *MakeCall(Arena &arena, std::string_view callee,
                      std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

namespace {

// =============================================================================
// §13.5.3 — default argument values
// =============================================================================
TEST(Functions, DefaultArgumentValue) {
  FuncFixture f;

  // function int add(input int a, input int b = 10);
  //   return a + b;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, {}, "b", MakeIntLit(f.arena, 10), {}},
  };
  auto *body_expr =
      MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "a"),
                 MakeIdent(f.arena, "b"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("add", func);

  // Call with both args: add(5, 20) => 25
  auto *call1 = MakeCall(f.arena, "add",
                         {MakeIntLit(f.arena, 5), MakeIntLit(f.arena, 20)});
  EXPECT_EQ(EvalExpr(call1, f.ctx, f.arena).ToUint64(), 25u);

  // Call with only first arg: add(5) => 5 + 10 = 15
  auto *call2 = MakeCall(f.arena, "add", {MakeIntLit(f.arena, 5)});
  EXPECT_EQ(EvalExpr(call2, f.ctx, f.arena).ToUint64(), 15u);
}

TEST(Functions, DefaultArgumentMultiple) {
  FuncFixture f;

  // function int compute(input int a = 1, input int b = 2, input int c = 3);
  //   return a + b + c;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "compute";
  func->func_args = {
      {Direction::kInput, false, {}, "a", MakeIntLit(f.arena, 1), {}},
      {Direction::kInput, false, {}, "b", MakeIntLit(f.arena, 2), {}},
      {Direction::kInput, false, {}, "c", MakeIntLit(f.arena, 3), {}},
  };
  auto *ab = MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "a"),
                        MakeIdent(f.arena, "b"));
  auto *abc =
      MakeBinary(f.arena, TokenKind::kPlus, ab, MakeIdent(f.arena, "c"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, abc));
  f.ctx.RegisterFunction("compute", func);

  // Call with no args: 1+2+3 = 6
  auto *call = MakeCall(f.arena, "compute", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

} // namespace
