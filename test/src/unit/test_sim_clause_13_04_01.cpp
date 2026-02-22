// §13.4.1: Return values and void functions

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
static Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: make an identifier expression.
static Expr* MakeIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: make a binary expression.
static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

// Helper: make a blocking assignment statement.
static Stmt* MakeAssign(Arena& arena, std::string_view lhs_name, Expr* rhs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = rhs;
  return s;
}

// Helper: make a return statement.
static Stmt* MakeReturn(Arena& arena, Expr* expr) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

// Helper: make a function call expression.
static Expr* MakeCall(Arena& arena, std::string_view callee,
                      std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

// Helper: make a function call with named arguments.
static Expr* MakeNamedCall(Arena& arena, std::string_view callee,
                           std::vector<Expr*> args,
                           std::vector<std::string_view> names) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  e->arg_names = std::move(names);
  return e;
}

namespace {

// =============================================================================
// §13.4.1 — void functions
// =============================================================================
TEST(Functions, VoidFunctionReturnsZero) {
  FuncFixture f;

  // function void set_val(input int a); endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_val";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kInput, false, {}, "a", nullptr, {}}};
  f.ctx.RegisterFunction("set_val", func);

  auto* call = MakeCall(f.arena, "set_val", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  // Void function should return 0.
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
