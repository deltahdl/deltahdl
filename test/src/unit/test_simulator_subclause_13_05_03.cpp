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
  LowerRunAndCheck(f, design,
                   {{"n.r1", 1u},
                    {"n.r2", 2u},
                    {"n.r3", 6u},
                    {"n.r4", 12u},
                    {"a", 6u},
                    {"w", 12u}});
}

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

TEST(DefaultArgumentSim, OutputDefaultBindsInTheDeclaringScope) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic a = 0;\n"
      "  task t1(output logic o = a); o = 1; endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic a = 0;\n"
      "  int r;\n"
      "  m u();\n"
      "  initial begin\n"
      "    u.t1();\n"
      "    #1 r = u.a * 10 + a;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(DefaultArgumentSim, TheClauseReadExampleFillsEachOmittedArgument) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  task read(int j = 0, int k, int data = 1 );\n"
                       "    $display(\"%0d %0d %0d\", j, k, data);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    read( , 5 );\n"
                       "    read( 2, 5 );\n"
                       "    read( , 5, );\n"
                       "    read( , 5, 7 );\n"
                       "    read( 1, 5, 2 );\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 5 1\n2 5 1\n0 5 1\n0 5 7\n1 5 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DefaultArgumentSim, ADefaultIsEvaluatedOnlyWhenTheCallUsesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int n, r;\n"
                       "  function automatic int bump();\n"
                       "    n++;\n"
                       "    return n * 10;\n"
                       "  endfunction\n"
                       "  class C;\n"
                       "    function int me(int k = bump());\n"
                       "      return k;\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C c = new();\n"
                       "  task automatic t(int k = bump(), int z = 0);\n"
                       "    $display(\"%0d %0d\", k, n);\n"
                       "  endtask\n"
                       "  function automatic int f(int k = bump());\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "  initial begin\n"

                       "    t(1);\n"
                       "    t(.k(2));\n"
                       "    t();\n"
                       "    t(, 3);\n"
                       "    t(.k());\n"
                       "    r = f(4);\n"
                       "    $display(\"%0d %0d\", r, n);\n"
                       "    r = f();\n"
                       "    $display(\"%0d %0d\", r, n);\n"
                       "    r = c.me(5);\n"
                       "    $display(\"%0d %0d\", r, n);\n"
                       "    r = c.me();\n"
                       "    $display(\"%0d %0d\", r, n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0\n2 0\n10 1\n20 2\n30 3\n4 3\n40 4\n5 4\n50 5\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DefaultArgumentSim, APackageClassOrInterfaceDefaultReadsItsOwnScope) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  int base = 3;\n"
                       "  function automatic int g(int k = base);\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "class C;\n"
                       "  int base = 5;\n"
                       "  function int me(int k = base);\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "interface ifc;\n"
                       "  int base = 9;\n"
                       "  function automatic int h(int k = base);\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "module m;\n"
                       "  int base = 100;\n"
                       "  C c = new();\n"
                       "  ifc i();\n"
                       "  initial begin\n"

                       "    c.base = 7;\n"
                       "    #1 $display(\"%0d %0d %0d\", pk::g(), c.me(), "
                       "i.h());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 7 9\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
