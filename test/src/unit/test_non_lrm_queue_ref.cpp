// §non-lrm:queue_ref


#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// ============================================================================
// Test fixture
// ============================================================================
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
static QueueObject* MakeQueue(SimFixture& f, std::string_view name,
                              const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  q->AssignFreshIds();
  return q;
}

// Register an automatic void function with given args and body.
static void RegAutoFunc(SimFixture& f, std::string_view name,
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
// A5: §6.22.2 — Type width check
// ============================================================================
// Queue elem_width=32 but function param is 16-bit ref → binding should fail
// and fall back to pass-by-value (write does not propagate).
TEST(QueueRef, WidthMismatchFallsBackToValue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void set_val(ref shortint v); v = 99; endfunction
  // shortint = 16-bit, queue elements are 32-bit.
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_val16";
  func->is_automatic = true;
  func->return_type.kind = DataTypeKind::kVoid;
  FunctionArg arg;
  arg.direction = Direction::kRef;
  arg.name = "v";
  arg.data_type.kind = DataTypeKind::kShortint;
  func->func_args = {arg};
  func->func_body_stmts = {MkAssign(f.arena, "v", MkIntLit(f.arena, 99))};
  f.ctx.RegisterFunction("set_val16", func);

  auto* call = MkCall(f.arena, "set_val16", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // Width mismatch → ref binding rejected → falls back to value.
  // q[1] should still be 20.
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
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

// Ref outdated by whole-queue assignment.
TEST(QueueRef, OutdatedByWholeAssign) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q = '{100, 200};   // whole-queue assignment
  //   v = 99;
  // endfunction
  //
  // We simulate the whole-queue assignment as: q.delete(); then push 100, 200.
  // (A real whole-queue assign goes through stmt_assign.cpp, which is harder to
  //  invoke from a function body in a unit test. This achieves the same effect:
  //  all element IDs are replaced → ref is outdated.)
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "delete", {})),
               MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "push_back",
                                                {MkIntLit(f.arena, 100)})),
               MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "push_back",
                                                {MkIntLit(f.arena, 200)})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {100, 200}. All original IDs are gone → ref is outdated.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 100u);
  EXPECT_EQ(q->elements[1].ToUint64(), 200u);
}

// ============================================================================
// A2: Queue ref binding — basic writeback
// ============================================================================
// Pass q[1] by ref, set v = 99, verify q[1] == 99.
TEST(QueueRef, BasicRefWriteback) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void set_val(ref int v); v = 99; endfunction
  RegAutoFunc(f, "set_val", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "set_val", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

// Ref survives push_front: push_front shifts indices but ref tracks element.
TEST(QueueRef, SurvivesPushFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.push_front(5);   // q[1] (val=20) shifts to q[2]
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "push_front",
                                                {MkIntLit(f.arena, 5)})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {5, 10, 99, 30}. Original q[1] (val=20) shifted to index 2.
  // The ref should have written 99 to index 2 (tracked via element ID).
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

}  // namespace
