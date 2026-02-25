// §13.5.2: Pass by reference

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

namespace {

// =============================================================================
// §13.5.2 — pass by reference
// =============================================================================
TEST(Functions, PassByRef) {
  FuncFixture f;

  // Variable "x" in caller scope
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 50);

  // function void add_ten(ref int r);
  //   r = r + 10;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ten";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kRef, false, {}, "r", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "r"),
                         MakeIntLit(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);

  // Call: add_ten(x) — should modify x directly (not via writeback)
  auto* call = MakeCall(f.arena, "add_ten", {MakeIdent(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 60u);
}

TEST(Functions, PassByRefReadsCaller) {
  FuncFixture f;

  // Variable "x" in caller scope
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 25);

  // function int read_ref(ref int r);
  //   return r * 3;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->func_args = {{Direction::kRef, false, {}, "r", nullptr, {}}};
  auto* body_expr = MakeBinary(f.arena, TokenKind::kStar,
                               MakeIdent(f.arena, "r"), MakeIntLit(f.arena, 3));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeIdent(f.arena, "x")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 75u);
}

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

// Pass q[1] by ref, return it, verify the function reads 20.
TEST(QueueRef, RefReadsCurrentValue) {
  QueueRefFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  // function automatic int read_ref(ref int v); return v; endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};
  func->func_body_stmts = {MkReturn(f.arena, MkIdent(f.arena, "v"))};
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MkCall(f.arena, "read_ref", {MkSelect(f.arena, "q", 1)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 20u);
}

}  // namespace
