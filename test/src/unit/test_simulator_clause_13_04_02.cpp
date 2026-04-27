#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeSim, StaticFunctionWithArgs) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "accum";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kInput, false, false, false, {}, "v", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "accum"),
                         MakeId(f.arena, "v"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "accum", rhs));
  f.ctx.RegisterFunction("accum", func);

  auto* c1 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 5)});
  EXPECT_EQ(EvalExpr(c1, f.ctx, f.arena).ToUint64(), 5u);

  auto* c2 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 3)});
  EXPECT_EQ(EvalExpr(c2, f.ctx, f.arena).ToUint64(), 8u);

  auto* c3 = MakeCall(f.arena, "accum", {MakeInt(f.arena, 2)});
  EXPECT_EQ(EvalExpr(c3, f.ctx, f.arena).ToUint64(), 10u);
}

// Static-function var persistence, automatic-function var freshness,
// the default-lifetime rule, the static-var-in-auto-func and
// auto-var-in-static-func cases, and the auto-module-inherits-auto rule
// are §6.21 lifetime semantics. The corresponding simulator tests live
// in test_simulator_clause_06_21.cpp.

TEST(FunctionLifetimeSim, RecursiveAutomaticFunction) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int factorial(input int n);\n"
      "    if (n <= 1)\n"
      "      factorial = 1;\n"
      "    else\n"
      "      factorial = factorial(n - 1) * n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = factorial(5);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 120u);
}

}  // namespace
