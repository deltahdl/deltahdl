// §13.5.2: Pass by reference

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

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
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "r"),
                         MakeInt(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);

  // Call: add_ten(x) — should modify x directly (not via writeback)
  auto* call = MakeCall(f.arena, "add_ten", {MakeId(f.arena, "x")});
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
                               MakeId(f.arena, "r"), MakeInt(f.arena, 3));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 75u);
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

// Pass q[1] by ref, return it, verify the function reads 20.
TEST(QueueRef, RefReadsCurrentValue) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  // function automatic int read_ref(ref int v); return v; endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};
  func->func_body_stmts = {MakeReturn(f.arena, MakeId(f.arena, "v"))};
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeSelect(f.arena, "q", 1)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 20u);
}

}  // namespace
