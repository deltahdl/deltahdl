// §13.5.4: Argument binding by name

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

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

namespace {

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
      MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "x"),
                 MakeId(f.arena, "y"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("sub", func);

  // Call with named args in reversed order: sub(.y(3), .x(10)) => 10 - 3 = 7
  auto* call = MakeNamedCall(f.arena, "sub",
                             {MakeInt(f.arena, 3), MakeInt(f.arena, 10)},
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
      {Direction::kInput, false, {}, "w", MakeInt(f.arena, 2), {}},
  };
  auto* body_expr =
      MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "a"),
                 MakeId(f.arena, "w"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("weighted", func);

  // Named call providing only "a", defaulting "w" => 7 * 2 = 14
  auto* call =
      MakeNamedCall(f.arena, "weighted", {MakeInt(f.arena, 7)}, {"a"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 14u);
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
      MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "target"),
                 MakeId(f.arena, "amount"));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "target", rhs));
  f.ctx.RegisterFunction("swap_add", func);

  // Call with named args in reversed order:
  // swap_add(.amount(5), .target(x))
  auto* call = MakeNamedCall(f.arena, "swap_add",
                             {MakeInt(f.arena, 5), MakeId(f.arena, "x")},
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
      {Direction::kInput, false, {}, "factor", MakeInt(f.arena, 3), {}},
  };
  auto* body = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "val"),
                          MakeId(f.arena, "factor"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("scale", func);

  // Named call with only "val", defaulting "factor":
  // scale(.val(7)) => 7 * 3 = 21
  auto* call =
      MakeNamedCall(f.arena, "scale", {MakeInt(f.arena, 7)}, {"val"});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 21u);
}

// --- named argument binding ---
TEST(SimA609, NamedArgCall) {
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

// --- mixed positional + named arguments ---
TEST(SimA609, MixedPositionalNamedArgs) {
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

// § list_of_arguments — named argument binding reorders args
TEST(SimA82, NamedArgBinding) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] sub(input logic [7:0] a, input logic [7:0] b);\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial x = sub(.b(8'd3), .a(8'd10));\n"
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

}  // namespace
