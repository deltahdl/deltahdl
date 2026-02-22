// §13.4.2: Static and automatic functions

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
// §13.3.1, §13.4.2 — static vs automatic lifetime
// =============================================================================
TEST(Functions, StaticFunctionPersistsVariables) {
  FuncFixture f;

  // function static int counter();
  //   counter = counter + 1;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  func->is_static = true;
  func->is_automatic = false;
  auto *rhs = MakeBinary(f.arena, TokenKind::kPlus,
                         MakeIdent(f.arena, "counter"), MakeIntLit(f.arena, 1));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "counter", rhs));
  f.ctx.RegisterFunction("counter", func);

  auto *call = MakeCall(f.arena, "counter", {});

  // First call: counter starts at 0, returns 0+1=1
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  // Second call: counter is still 1 from last call, returns 1+1=2
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 2u);
  // Third call: counter is 2, returns 3
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 3u);
}

TEST(Functions, AutomaticFunctionFreshVariables) {
  FuncFixture f;

  // function automatic int counter();
  //   counter = counter + 1;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  func->is_automatic = true;
  func->is_static = false;
  auto *rhs = MakeBinary(f.arena, TokenKind::kPlus,
                         MakeIdent(f.arena, "counter"), MakeIntLit(f.arena, 1));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "counter", rhs));
  f.ctx.RegisterFunction("counter", func);

  auto *call = MakeCall(f.arena, "counter", {});

  // Each call starts fresh: 0+1=1 every time.
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Functions, StaticFunctionWithArgs) {
  FuncFixture f;

  // function static int accum(input int v);
  //   accum = accum + v;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "accum";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  auto *rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "accum"),
                         MakeIdent(f.arena, "v"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "accum", rhs));
  f.ctx.RegisterFunction("accum", func);

  // accum(5) => 0 + 5 = 5
  auto *c1 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 5)});
  EXPECT_EQ(EvalExpr(c1, f.ctx, f.arena).ToUint64(), 5u);
  // accum(3) => 5 + 3 = 8
  auto *c2 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 3)});
  EXPECT_EQ(EvalExpr(c2, f.ctx, f.arena).ToUint64(), 8u);
  // accum(2) => 8 + 2 = 10
  auto *c3 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 2)});
  EXPECT_EQ(EvalExpr(c3, f.ctx, f.arena).ToUint64(), 10u);
}

} // namespace
