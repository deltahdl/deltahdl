#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

static ModuleItem* MakeCounterFunc(Arena& arena) {
  auto* func = arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "counter";
  auto* rhs = MakeBinary(arena, TokenKind::kPlus, MakeId(arena, "counter"),
                         MakeInt(arena, 1));
  func->func_body_stmts.push_back(MakeAssign(arena, "counter", rhs));
  return func;
}

namespace {

TEST(Functions, StaticFunctionPersistsVariables) {
  FuncFixture f;

  auto* func = MakeCounterFunc(f.arena);
  func->is_static = true;
  func->is_automatic = false;
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);

  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 2u);

  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 3u);
}

TEST(Functions, AutomaticFunctionFreshVariables) {
  FuncFixture f;

  auto* func = MakeCounterFunc(f.arena);
  func->is_automatic = true;
  func->is_static = false;
  f.ctx.RegisterFunction("counter", func);

  auto* call = MakeCall(f.arena, "counter", {});

  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Functions, StaticFunctionWithArgs) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "accum";
  func->is_static = true;
  func->is_automatic = false;
  func->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
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

TEST(Sim1342, StaticFunctionVarsPersist) {
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

TEST(Sim1342, AutomaticFunctionVarsFresh) {
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

TEST(Sim1342, DefaultFunctionIsStatic) {
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

TEST(Sim1342, StaticVarInAutoFuncPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int get_id();\n"
      "    static int next_id = 0;\n"
      "    next_id = next_id + 1;\n"
      "    return next_id;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(Sim1342, AutoVarInStaticFuncFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int compute();\n"
      "    automatic int tmp = 10;\n"
      "    tmp = tmp + 1;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = compute();\n"
      "    result = compute();\n"
      "  end\n"
      "endmodule\n",
      "result");

  EXPECT_EQ(val, 11u);
}

TEST(Sim1342, RecursiveAutoFunction) {
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

}
