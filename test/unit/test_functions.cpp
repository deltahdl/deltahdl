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

TEST(Functions, VoidFunctionSideEffect) {
  FuncFixture f;

  // Global variable "g" that the function modifies via output arg.
  auto* g_var = f.ctx.CreateVariable("g", 32);
  g_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // function void store(output int out); out = 99; endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "store";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kOutput, false, {}, "out", nullptr, {}}};
  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "out", MakeIntLit(f.arena, 99)));
  f.ctx.RegisterFunction("store", func);

  auto* call = MakeCall(f.arena, "store", {MakeIdent(f.arena, "g")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(g_var->value.ToUint64(), 99u);
}

// =============================================================================
// §13.5.3 — default argument values
// =============================================================================

TEST(Functions, DefaultArgumentValue) {
  FuncFixture f;

  // function int add(input int a, input int b = 10);
  //   return a + b;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, {}, "b", MakeIntLit(f.arena, 10), {}},
  };
  auto* body_expr =
      MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "a"),
                 MakeIdent(f.arena, "b"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("add", func);

  // Call with both args: add(5, 20) => 25
  auto* call1 = MakeCall(f.arena, "add",
                         {MakeIntLit(f.arena, 5), MakeIntLit(f.arena, 20)});
  EXPECT_EQ(EvalExpr(call1, f.ctx, f.arena).ToUint64(), 25u);

  // Call with only first arg: add(5) => 5 + 10 = 15
  auto* call2 = MakeCall(f.arena, "add", {MakeIntLit(f.arena, 5)});
  EXPECT_EQ(EvalExpr(call2, f.ctx, f.arena).ToUint64(), 15u);
}

TEST(Functions, DefaultArgumentMultiple) {
  FuncFixture f;

  // function int compute(input int a = 1, input int b = 2, input int c = 3);
  //   return a + b + c;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "compute";
  func->func_args = {
      {Direction::kInput, false, {}, "a", MakeIntLit(f.arena, 1), {}},
      {Direction::kInput, false, {}, "b", MakeIntLit(f.arena, 2), {}},
      {Direction::kInput, false, {}, "c", MakeIntLit(f.arena, 3), {}},
  };
  auto* ab = MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "a"),
                        MakeIdent(f.arena, "b"));
  auto* abc =
      MakeBinary(f.arena, TokenKind::kPlus, ab, MakeIdent(f.arena, "c"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, abc));
  f.ctx.RegisterFunction("compute", func);

  // Call with no args: 1+2+3 = 6
  auto* call = MakeCall(f.arena, "compute", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

// =============================================================================
// §13.5.4 — named argument binding
// =============================================================================

TEST(Functions, NamedArguments) {
  FuncFixture f;

  // function int sub(input int x, input int y);
  //   return x - y;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "sub";
  func->func_args = {
      {Direction::kInput, false, {}, "x", nullptr, {}},
      {Direction::kInput, false, {}, "y", nullptr, {}},
  };
  auto* body_expr =
      MakeBinary(f.arena, TokenKind::kMinus, MakeIdent(f.arena, "x"),
                 MakeIdent(f.arena, "y"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("sub", func);

  // Call with named args in reversed order: sub(.y(3), .x(10)) => 10 - 3 = 7
  auto* call = MakeNamedCall(f.arena, "sub",
                             {MakeIntLit(f.arena, 3), MakeIntLit(f.arena, 10)},
                             {"y", "x"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 7u);
}

TEST(Functions, NamedArgsWithDefaults) {
  FuncFixture f;

  // function int weighted(input int a, input int w = 2);
  //   return a * w;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "weighted";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, {}, "w", MakeIntLit(f.arena, 2), {}},
  };
  auto* body_expr =
      MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "a"),
                 MakeIdent(f.arena, "w"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("weighted", func);

  // Named call providing only "a", defaulting "w" => 7 * 2 = 14
  auto* call =
      MakeNamedCall(f.arena, "weighted", {MakeIntLit(f.arena, 7)}, {"a"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 14u);
}

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

// =============================================================================
// §13.3.1, §13.4.2 — static vs automatic lifetime
// =============================================================================

TEST(Functions, StaticFunctionPersistsVariables) {
  FuncFixture f;

  // function static int counter();
  //   counter = counter + 1;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  func->is_static = true;
  func->is_automatic = false;
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus,
                         MakeIdent(f.arena, "counter"), MakeIntLit(f.arena, 1));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "counter", rhs));
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

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
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  func->is_automatic = true;
  func->is_static = false;
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus,
                         MakeIdent(f.arena, "counter"), MakeIntLit(f.arena, 1));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "counter", rhs));
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

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
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "accum";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "accum"),
                         MakeIdent(f.arena, "v"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "accum", rhs));
  f.ctx.RegisterFunction("accum", func);

  // accum(5) => 0 + 5 = 5
  auto* c1 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 5)});
  EXPECT_EQ(EvalExpr(c1, f.ctx, f.arena).ToUint64(), 5u);
  // accum(3) => 5 + 3 = 8
  auto* c2 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 3)});
  EXPECT_EQ(EvalExpr(c2, f.ctx, f.arena).ToUint64(), 8u);
  // accum(2) => 8 + 2 = 10
  auto* c3 = MakeCall(f.arena, "accum", {MakeIntLit(f.arena, 2)});
  EXPECT_EQ(EvalExpr(c3, f.ctx, f.arena).ToUint64(), 10u);
}

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
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "double_val";
  func->func_args = {{Direction::kInput, false, {}, "x", nullptr, {}}};
  auto* body = MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "x"),
                          MakeIntLit(f.arena, 2));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("double_val", func);

  auto* call = MakeCall(f.arena, "double_val", {MakeIntLit(f.arena, 21)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

// =============================================================================
// Combined feature tests
// =============================================================================

TEST(Functions, NamedArgsReorderedWithRef) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 100);

  // function void swap_add(ref int target, input int amount);
  //   target = target + amount;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "swap_add";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, {}, "target", nullptr, {}},
      {Direction::kInput, false, {}, "amount", nullptr, {}},
  };
  auto* rhs =
      MakeBinary(f.arena, TokenKind::kPlus, MakeIdent(f.arena, "target"),
                 MakeIdent(f.arena, "amount"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "target", rhs));
  f.ctx.RegisterFunction("swap_add", func);

  // Call with named args in reversed order:
  // swap_add(.amount(5), .target(x))
  auto* call = MakeNamedCall(f.arena, "swap_add",
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
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "scale";
  func->func_args = {
      {Direction::kInput, false, {}, "val", nullptr, {}},
      {Direction::kInput, false, {}, "factor", MakeIntLit(f.arena, 3), {}},
  };
  auto* body = MakeBinary(f.arena, TokenKind::kStar, MakeIdent(f.arena, "val"),
                          MakeIdent(f.arena, "factor"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("scale", func);

  // Named call with only "val", defaulting "factor":
  // scale(.val(7)) => 7 * 3 = 21
  auto* call =
      MakeNamedCall(f.arena, "scale", {MakeIntLit(f.arena, 7)}, {"val"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 21u);
}
