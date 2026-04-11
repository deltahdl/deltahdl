#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

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

namespace {

TEST(NamedArgBindingSimulation, NamedArgsWithDefaults) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "weighted";
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "a", nullptr, {}},
      {Direction::kInput, false, false, false, {}, "w", MakeInt(f.arena, 2), {}},
  };
  auto* body_expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "a"),
                               MakeId(f.arena, "w"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("weighted", func);

  auto* call = MakeNamedCall(f.arena, "weighted", {MakeInt(f.arena, 7)}, {"a"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 14u);
}

TEST(NamedArgBindingSimulation, NamedArgsReorderedWithRef) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "swap_add";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "target", nullptr, {}},
      {Direction::kInput, false, false, false, {}, "amount", nullptr, {}},
  };
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "target"),
                         MakeId(f.arena, "amount"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "target", rhs));
  f.ctx.RegisterFunction("swap_add", func);

  auto* call = MakeNamedCall(f.arena, "swap_add",
                             {MakeInt(f.arena, 5), MakeId(f.arena, "x")},
                             {"amount", "target"});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 105u);
}

TEST(SubroutineCallSim, NamedArgCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] sub(input logic [7:0] a, input logic [7:0] b);\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = sub(.b(8'd3), .a(8'd10));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(SubroutineCallSim, MixedPositionalNamedArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add3(input logic [7:0] a, input logic [7:0] b,\n"
      "                            input logic [7:0] c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add3(8'd1, 8'd2, .c(8'd3));\n"
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

TEST(SubroutineCallSim, NamedArgsOmitDefaultedArg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] scale(input logic [7:0] val,\n"
      "                             input logic [7:0] factor = 8'd3);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = scale(.val(8'd7));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(SubroutineCallSim, NamedArgTaskOutputWriteback) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  task swap(input logic [7:0] x, input logic [7:0] y,\n"
      "            output logic [7:0] ox, output logic [7:0] oy);\n"
      "    ox = y;\n"
      "    oy = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    swap(.y(8'd20), .x(8'd10), .oy(b), .ox(a));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 20u);
  EXPECT_EQ(vb->value.ToUint64(), 10u);
}

}  // namespace
