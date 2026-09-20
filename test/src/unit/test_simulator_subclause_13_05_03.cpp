#include <gtest/gtest.h>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(Functions, DefaultArgumentValue) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add";
  // §13.4: a function whose return type is left implicit returns a `logic`
  // scalar, and §13.4.1's internal variable then truncates the returned
  // expression to that one bit. This fixture is about how an argument reaches
  // the body, not about an implicit return type, so it declares one wide
  // enough to carry the value the call is checked for.
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "a", nullptr, {}},
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "b",
       MakeInt(f.arena, 10),
       {}},
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
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "a",
       MakeInt(f.arena, 1),
       {}},
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "b",
       MakeInt(f.arena, 2),
       {}},
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "c",
       MakeInt(f.arena, 3),
       {}},
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
  LowerRunAndCheck(f, design, {{"x", 10u}, {"y", 15u}});
}

TEST(DefaultArgumentSim, DefaultExpressionEvaluated) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "get_size";
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "size",
       MakeBinary(f.arena, TokenKind::kStar, MakeInt(f.arena, 8),
                  MakeInt(f.arena, 4)),
       {}},
  };
  func->func_body_stmts.push_back(MakeReturn(f.arena, MakeId(f.arena, "size")));
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
  LowerRunAndCheck(f, design, {{"x", 15u}});
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
  LowerRunAndCheck(f, design, {{"a", 42u}});
}

TEST(DefaultArgumentSim, DefaultReevaluatedEachCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] base;\n"
      "  logic [7:0] r1, r2;\n"
      "  function logic [7:0] read(input logic [7:0] x = base);\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    base = 8'd10;\n"
      "    r1 = read();\n"
      "    base = 8'd20;\n"
      "    r2 = read();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 20u}});
}

TEST(DefaultArgumentSim, EmptyPlaceholderUsesDefault) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "calc";
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "j",
       MakeInt(f.arena, 0),
       {}},
      {Direction::kInput, false, false, false, {}, "k", nullptr, {}},
      {Direction::kInput,
       false,
       false,
       false,
       {},
       "data",
       MakeInt(f.arena, 1),
       {}},
  };
  auto* jk = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "j"),
                        MakeId(f.arena, "k"));
  auto* body =
      MakeBinary(f.arena, TokenKind::kPlus, jk, MakeId(f.arena, "data"));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body));
  f.ctx.RegisterFunction("calc", func);

  auto* call = MakeCall(f.arena, "calc", {nullptr, MakeInt(f.arena, 5)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 6u);
}

// §13.5.3's own example, in its two-top shape: n enables m's tasks by
// hierarchical name and reads m's variables the same way (§23.6 lets the
// complete path start at a top-level module from a parallel hierarchy), and
// each default actual binds in m, the scope of the declaration. The reads
// before the enables give m's initial 1 and 2, and after them the 6 the
// output default wrote into m's `a` and the 12 the inout default left in
// `w`; a reference into m that reaches nothing reads 0 for all four and
// leaves `a` and `w` at 1 and 2.
TEST(DefaultArgumentSim, DefaultBoundInDeclaringTopFromParallelTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module m;\n"
      "  int a = 1, w = 2;\n"
      "  task t1(output int o = a); o = 6; endtask\n"
      "  task t3(inout int io = w); io = io * 6; endtask\n"
      "endmodule\n"
      "module n;\n"
      "  int r1, r2, r3, r4;\n"
      "  initial begin\n"
      "    r1 = m.a;\n"
      "    r2 = m.w;\n"
      "    m.t1();\n"
      "    m.t3();\n"
      "    r3 = m.a;\n"
      "    r4 = m.w;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 1u}, {"r2", 2u}, {"r3", 6u}, {"r4", 12u}, {"a", 6u}, {"w", 12u}});
}

// §23.6: a write through the same path lands in m: n's `m.a = 7` is what m's
// own process reads a time step later, 107 rather than the 101 its initial
// value gives when the write reaches nothing.
TEST(DefaultArgumentSim, WriteIntoParallelTopByHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module m;\n"
      "  int a = 1, b;\n"
      "  initial #1 b = a + 100;\n"
      "endmodule\n"
      "module n;\n"
      "  initial m.a = 7;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 7u}, {"b", 107u}});
}

}  // namespace
