// §13.5.3: Default argument values

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

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
      {Direction::kInput, false, {}, "b", MakeInt(f.arena, 10), {}},
  };
  auto* body_expr =
      MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                 MakeId(f.arena, "b"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("add", func);

  // Call with both args: add(5, 20) => 25
  auto* call1 = MakeCall(f.arena, "add",
                         {MakeInt(f.arena, 5), MakeInt(f.arena, 20)});
  EXPECT_EQ(EvalExpr(call1, f.ctx, f.arena).ToUint64(), 25u);

  // Call with only first arg: add(5) => 5 + 10 = 15
  auto* call2 = MakeCall(f.arena, "add", {MakeInt(f.arena, 5)});
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
      {Direction::kInput, false, {}, "a", MakeInt(f.arena, 1), {}},
      {Direction::kInput, false, {}, "b", MakeInt(f.arena, 2), {}},
      {Direction::kInput, false, {}, "c", MakeInt(f.arena, 3), {}},
  };
  auto* ab = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto* abc =
      MakeBinary(f.arena, TokenKind::kPlus, ab, MakeId(f.arena, "c"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, abc));
  f.ctx.RegisterFunction("compute", func);

  // Call with no args: 1+2+3 = 6
  auto* call = MakeCall(f.arena, "compute", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

// --- function with default argument ---
TEST(SimA609, FunctionDefaultArg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] inc(input logic [7:0] v, input logic [7:0] n = "
      "8'd1);\n"
      "    return v + n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = inc(8'd5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

}  // namespace
