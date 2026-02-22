// §13.5: Subroutine calls and argument passing

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

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

// Helper: make a blocking assignment statement.
static Stmt *MakeAssign(Arena &arena, std::string_view lhs_name, Expr *rhs) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = rhs;
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

TEST(Functions, VoidFunctionSideEffect) {
  FuncFixture f;

  // Global variable "g" that the function modifies via output arg.
  auto *g_var = f.ctx.CreateVariable("g", 32);
  g_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // function void store(output int out); out = 99; endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "store";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kOutput, false, {}, "out", nullptr, {}}};
  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "out", MakeIntLit(f.arena, 99)));
  f.ctx.RegisterFunction("store", func);

  auto *call = MakeCall(f.arena, "store", {MakeIdent(f.arena, "g")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(g_var->value.ToUint64(), 99u);
}

}  // namespace
