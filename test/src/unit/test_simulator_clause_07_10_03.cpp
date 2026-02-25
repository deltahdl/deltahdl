// §7.10.3: Persistence of references to elements of a queue

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
// A3: Outdating — writeback suppressed / preserved
// ============================================================================
// Ref outdated by delete(1): q.delete(1) removes the bound element.
// Write 99 to ref — should NOT propagate back.
TEST(QueueRef, OutdatedByDelete) {
  QueueRefFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.delete(1);
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "delete",
                                                {MkIntLit(f.arena, 1)})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {10, 30}. Element 20 was deleted → ref is outdated.
  // 99 should NOT appear in the queue.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// Ref outdated by pop_front when the ref points to element 0.
TEST(QueueRef, OutdatedByPopFront) {
  QueueRefFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.pop_front();   // removes q[0] (the bound element)
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "pop_front", {})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {20, 30}. Element 10 was popped → ref is outdated.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

static Expr* LspId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* LspSelect(Arena& arena, Expr* base, Expr* index) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

static Expr* LspInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Ref survives push_back: push_back never outdates refs.
TEST(QueueRef, SurvivesPushBack) {
  QueueRefFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.push_back(40);
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "push_back",
                                                {MkIntLit(f.arena, 40)})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {10, 99, 30, 40}. q[1] should be 99 (ref survived push_back).
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

}  // namespace
