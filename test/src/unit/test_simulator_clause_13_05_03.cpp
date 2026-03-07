#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(Functions, DefaultArgumentValue) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, {}, "b", MakeInt(f.arena, 10), {}},
  };
  auto* body_expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                               MakeId(f.arena, "b"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("add", func);

  auto* call1 =
      MakeCall(f.arena, "add", {MakeInt(f.arena, 5), MakeInt(f.arena, 20)});
  EXPECT_EQ(EvalExpr(call1, f.ctx, f.arena).ToUint64(), 25u);

  auto* call2 = MakeCall(f.arena, "add", {MakeInt(f.arena, 5)});
  EXPECT_EQ(EvalExpr(call2, f.ctx, f.arena).ToUint64(), 15u);
}

TEST(Functions, DefaultArgumentMultiple) {
  FuncFixture f;

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
  auto* abc = MakeBinary(f.arena, TokenKind::kPlus, ab, MakeId(f.arena, "c"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, abc));
  f.ctx.RegisterFunction("compute", func);

  auto* call = MakeCall(f.arena, "compute", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

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

// §13.5.3: Default arg with explicit override in full integration.
TEST(Sim1353, DefaultArgOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  function logic [7:0] scale(input logic [7:0] v,\n"
      "                             input logic [7:0] factor = 8'd2);\n"
      "    return v * factor;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = scale(8'd5);\n"
      "    y = scale(8'd5, 8'd3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 10u);
  EXPECT_EQ(yv->value.ToUint64(), 15u);
}

}  // namespace
