// §13.5.2: Pass by reference

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// ============================================================================
// Test fixture
// ============================================================================
struct QueueRefFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// ============================================================================
// AST helpers
// ============================================================================
static Expr* MkIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MkIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Build a[i] (kSelect).
static Expr* MkSelect(Arena& arena, std::string_view base, uint64_t idx) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MkIdent(arena, base);
  e->index = MkIntLit(arena, idx);
  return e;
}

// Build a.method(args...) (kCall with kMemberAccess lhs).
static Expr* MkMethodCall(Arena& arena, std::string_view obj,
                          std::string_view method, std::vector<Expr*> args) {
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MkIdent(arena, obj);
  access->rhs = MkIdent(arena, method);

  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = access;
  call->args = std::move(args);
  return call;
}

static Expr* MkCall(Arena& arena, std::string_view callee,
                    std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

// Build: lhs_name = rhs;
static Stmt* MkAssign(Arena& arena, std::string_view lhs_name, Expr* rhs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MkIdent(arena, lhs_name);
  s->rhs = rhs;
  return s;
}

// Build: expr; (expression statement, e.g. method call).
static Stmt* MkExprStmt(Arena& arena, Expr* expr) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kExprStmt;
  s->expr = expr;
  return s;
}

static Stmt* MkReturn(Arena& arena, Expr* expr) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kReturn;
  s->expr = expr;
  return s;
}

// ============================================================================
// Queue helper: populate a queue with integer values.
// ============================================================================
static QueueObject* MakeQueue(QueueRefFixture& f, std::string_view name,
                              const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  q->AssignFreshIds();
  return q;
}

// Register an automatic void function with given args and body.
static void RegAutoFunc(QueueRefFixture& f, std::string_view name,
                        std::vector<FunctionArg> args,
                        std::vector<Stmt*> body) {
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = name;
  func->is_automatic = true;
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = std::move(args);
  func->func_body_stmts = std::move(body);
  f.ctx.RegisterFunction(name, func);
}

namespace {

// ============================================================================
// A4: §6.21 — ValidateRefLifetime
// ============================================================================
// A static function with ref arg should produce a diagnostic error.
TEST(QueueRef, RejectRefInStaticFunc) {
  QueueRefFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "bad_func";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_TRUE(f.diag.HasErrors());
}

// An automatic function with ref arg should be accepted.
TEST(QueueRef, AcceptRefInAutoFunc) {
  QueueRefFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "good_func";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};

  ValidateRefLifetime(func, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
