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
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "v", nullptr, {}}};
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

// §13.4.2: a function with no explicit lifetime, defined within a module that
// is declared automatic, is implicitly automatic. It is therefore reentrant,
// so this recursive function computes 5! correctly; a static function would
// clobber its operand across the nested calls.
TEST(FunctionLifetimeSim, DefaultFunctionInAutomaticModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int factorial(input int n);\n"
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

// §13.4.2: a function with no explicit lifetime, in an ordinary (non-automatic)
// module, defaults to static — its items are statically allocated and shared
// across successive calls. The implicit return variable therefore accumulates,
// so the second call sees the first call's result (5 + 3 = 8). A reentrant
// allocation would reset it and yield 3.
TEST(FunctionLifetimeSim, DefaultLifetimeFunctionRetainsStaticStorage) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  function int accum(input int v);\n"
      "    accum = accum + v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = accum(5);\n"
      "    r2 = accum(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 8u);
}

// §13.4.2: a local declared static inside an automatic function overrides the
// function's lifetime for that variable, so it is allocated once and retains
// its value across calls. acc accumulates 5 then 3, so the second call returns
// 8; if the static override were ignored the per-call value would be 3.
TEST(FunctionLifetimeSim, StaticLocalInAutomaticFunctionRetainsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  function automatic int tally(input int v);\n"
      "    static int acc = 0;\n"
      "    acc = acc + v;\n"
      "    return acc;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = tally(5);\n"
      "    r2 = tally(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 8u);
}

}  // namespace
