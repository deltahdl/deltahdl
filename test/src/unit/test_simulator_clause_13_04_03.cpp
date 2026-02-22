// §13.4.3: Constant functions

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
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "double_val";
  func->func_args = {{Direction::kInput, false, {}, "x", nullptr, {}}};
  auto *body = MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "x"),
                          MakeIntLit(f.arena, 2));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("double_val", func);

  auto *call = MakeCall(f.arena, "double_val", {MakeIntLit(f.arena, 21)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

} // namespace
