#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(Functions, DefaultArgumentValue) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, false, false, {}, "b", MakeInt(f.arena, 10), {}},
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
      {Direction::kInput, false, false, false, {}, "a", MakeInt(f.arena, 1), {}},
      {Direction::kInput, false, false, false, {}, "b", MakeInt(f.arena, 2), {}},
      {Direction::kInput, false, false, false, {}, "c", MakeInt(f.arena, 3), {}},
  };
  auto* ab = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto* abc = MakeBinary(f.arena, TokenKind::kPlus, ab, MakeId(f.arena, "c"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, abc));
  f.ctx.RegisterFunction("compute", func);

  auto* call = MakeCall(f.arena, "compute", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

TEST(DefaultArgumentSim, DefaultArgOverride) {
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

TEST(DefaultArgumentSim, DefaultExpressionEvaluated) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "get_size";
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "size",
       MakeBinary(f.arena, TokenKind::kStar, MakeInt(f.arena, 8),
                  MakeInt(f.arena, 4)),
       {}},
  };
  func->func_body_stmts.push_back(
      MakeReturn(f.arena, MakeId(f.arena, "size")));
  f.ctx.RegisterFunction("get_size", func);

  auto* call = MakeCall(f.arena, "get_size", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 32u);
}

TEST(DefaultArgumentSim, DefaultEvalInDeclaringScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] base;\n"
      "  function logic [7:0] add(input logic [7:0] a,\n"
      "                           input logic [7:0] b = base);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    base = 8'd10;\n"
      "    x = add(8'd5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  ASSERT_NE(xv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 15u);
}

TEST(DefaultArgumentSim, TaskOutputArgWriteback) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  task t1(output logic [7:0] o = a);\n"
      "    o = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    t1();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* av = f.ctx.FindVariable("a");
  ASSERT_NE(av, nullptr);
  EXPECT_EQ(av->value.ToUint64(), 42u);
}

TEST(DefaultArgumentSim, EmptyPlaceholderUsesDefault) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "calc";
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "j", MakeInt(f.arena, 0),
       {}},
      {Direction::kInput, false, false, false, {}, "k", nullptr, {}},
      {Direction::kInput, false, false, false, {}, "data",
       MakeInt(f.arena, 1), {}},
  };
  auto* jk = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "j"),
                         MakeId(f.arena, "k"));
  auto* body = MakeBinary(f.arena, TokenKind::kPlus, jk,
                           MakeId(f.arena, "data"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("calc", func);

  auto* call = MakeCall(f.arena, "calc", {nullptr, MakeInt(f.arena, 5)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

}  // namespace
