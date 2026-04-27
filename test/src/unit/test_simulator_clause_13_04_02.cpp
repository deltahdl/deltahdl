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

TEST(FunctionLifetimeSim, StaticFunctionVarsPersist) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionLifetimeSim, AutomaticFunctionVarsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(FunctionLifetimeSim, DefaultFunctionIsStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

// Static-var-in-auto-func persistence and auto-var-in-static-func
// freshness are §6.21 lifetime semantics; the corresponding simulator
// tests (ExplicitStaticInAutoFuncBlockPersists,
// ExplicitAutoInStaticFuncBlockFresh) live in
// test_simulator_clause_06_21.cpp.

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

TEST(FunctionLifetimeSim, DefaultLifetimeInAutomaticModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

}  // namespace
