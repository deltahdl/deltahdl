#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(TaggedUnionEval, TaggedUnionNoTagSetAccessesNormally) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "simple_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"x", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("simple_u", uinfo);

  MakeVar(f, "v", 8, 0xFF);
  f.ctx.SetVariableStructType("v", "simple_u");

  auto* access_x = f.arena.Create<Expr>();
  access_x->kind = ExprKind::kMemberAccess;
  access_x->lhs = MakeId(f.arena, "v");
  access_x->rhs = MakeId(f.arena, "x");
  auto result_x = EvalExpr(access_x, f.ctx, f.arena);
  EXPECT_EQ(result_x.ToUint64(), 0xFFu);
}

TEST(TaggedUnionEval, TaggedExprWithValue) {
  SimFixture f;

  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Valid";
  tagged->rhs = member;
  tagged->lhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(TaggedUnionEval, TaggedExprVoidMember) {
  SimFixture f;

  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Invalid";
  tagged->rhs = member;
  tagged->lhs = nullptr;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(TaggedUnionEval, TaggedAssignSetsTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 7;\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(TaggedUnionEval, TaggedAssignOverwriteAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int X; int Y; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged X 100;\n"
      "    u = tagged Y 200;\n"
      "    result = u.Y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(TaggedUnionEval, MatchingMemberWriteUpdatesValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_wr_ok";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_wr_ok", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x00);
  f.ctx.SetVariableStructType("u", "u_wr_ok");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "a");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x5A);

  WriteStructField(lhs, rhs_val, f.ctx);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(TaggedUnionEval, MismatchedWriteEmitsDiagnosticAndKeepsValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_diag_w";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_diag_w", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x33);
  f.ctx.SetVariableStructType("u", "u_diag_w");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "b");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x77);

  EXPECT_FALSE(f.diag.HasErrors());
  WriteStructField(lhs, rhs_val, f.ctx);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: assigning member", 0, "11.9"));
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
}

TEST(TaggedUnionEval, VoidMemberThenValueMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o;\n"
      "  int result;\n"
      "  initial begin\n"
      "    o = tagged None;\n"
      "    o = tagged Some 77;\n"
      "    result = o.Some;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(TaggedUnionEval, DeclarationInitializerHoldsMemberValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.A;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(TaggedUnionEval, DeclarationInitializerSetsTagForMemberCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 5, "11.9"));
}

TEST(TaggedUnionEval, ProceduralAssignThenMismatchedReadErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 5;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 7, "11.9"));
}

TEST(TaggedUnionEval, UninitializedTaggedUnionHasNoActiveTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NE(f.ctx.FindVariable("u"), nullptr);
  EXPECT_TRUE(f.ctx.GetVariableTag("u").empty());
}

TEST(TaggedUnionEval, CastContextTaggedExprEvaluates) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = U'(tagged A 9);\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(TaggedUnionEval, TaggedMemberValueFromStructAssignmentPattern) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [4:0] reg1; bit [4:0] reg2;\n"
      "                          bit [4:0] regd; } add_t;\n"
      "  typedef union tagged { add_t Add; bit [14:0] Jmp; } Instr;\n"
      "  Instr i1;\n"
      "  int result;\n"
      "  initial begin\n"
      "    i1 = tagged Add '{5, 9, 3};\n"
      "    result = i1.Add.reg2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(TaggedUnionEval, VoidMemberDeclarationInitializerSetsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o = tagged None;\n"
      "  int result;\n"
      "  initial result = o.Some;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 5, "11.9"));
}

TEST(TaggedUnionEval, MismatchedReadNames11_9) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int P; int Q; } TU;\n"
      "  TU u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged P 7;\n"
      "    result = u.Q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 7, "11.9"));
}

TEST(TaggedUnionEval, MismatchedWriteNames11_9) {
  SimFixture f;
  StructTypeInfo uinfo;
  uinfo.type_name = "u_sub_w";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"p", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"q", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_sub_w", uinfo);

  MakeVar(f, "us", 8, 0x11);
  f.ctx.SetVariableStructType("us", "u_sub_w");
  f.ctx.SetVariableTag("us", "p");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "us");
  lhs->rhs = MakeId(f.arena, "q");
  WriteStructField(lhs, MakeLogic4VecVal(f.arena, 8, 0x22), f.ctx);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: assigning member", 0, "11.9"));
}

TEST(TaggedUnionEval, ChildInstanceDeclarationInitializerTagChecksMemberRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid (-7);\n"
      "  u_t w = tagged Invalid;\n"
      "  int x;\n"
      "  int y;\n"
      "  initial begin\n"
      "    x = u.Valid;\n"
      "    y = w.Valid;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("m.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 9, "11.9"));
}

TEST(TaggedUnionEval, ChildInstanceProceduralTagReplacesDeclarationTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int x;\n"
      "  int y;\n"
      "  initial begin\n"
      "    u = tagged B 9;\n"
      "    x = u.B;\n"
      "    y = u.A;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("m.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 9, "11.9"));
}

TEST(TaggedUnionEval, ChildInstanceDeclarationInitializerPrintsTagAndValue) {
  SimFixture f;
  auto out = RunCapture(
      "module M;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid (-7);\n"
      "  initial $display(\"%p\", u);\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:-7}\n");
}

TEST(TaggedUnionEval, ByValueFormalCarriesTheActualsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid (-7);\n"
      "  u_t w = tagged Invalid;\n"
      "  int x;\n"
      "  int y;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f(u);\n"
      "    y = f(w);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "tagged union 'a' which currently has tag 'Valid'",
                             8, "11.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 8, "11.9"));
}

TEST(TaggedUnionEval, OutputFormalCarriesItsTagBackToTheActual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u = tagged Other 1;\n"
      "  int x;\n"
      "  int y;\n"
      "  task retag(output u_t o);\n"
      "    o = tagged Valid 4;\n"
      "  endtask\n"
      "  initial begin\n"
      "    retag(u);\n"
      "    x = u.Valid;\n"
      "    y = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 4u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 11, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            12, "11.9"));
}

TEST(TaggedUnionEval, ByValueFormalPrintsTheActualsTagAndValue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid (-7);\n"
      "  function void show(u_t a);\n"
      "    $display(\"%p\", a);\n"
      "  endfunction\n"
      "  initial show(u);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:-7}\n");
}

TEST(TaggedUnionEval, TaggedExprActualBindsTheFormalsLayoutAndTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial x = f(tagged Valid (-7));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 5, "11.9"));
}

TEST(TaggedUnionEval, TaggedExprActualOfVoidMemberIsCheckedInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int y;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial y = f(tagged Invalid);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 5, "11.9"));
}

TEST(TaggedUnionEval, TaggedExprActualNarrowMemberReadsItsOwnWindow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; bit [7:0] Small; int Other; }"
      " u_t;\n"
      "  int z;\n"
      "  int w;\n"
      "  function int g(u_t a);\n"
      "    return {a.Small, a.Small};\n"
      "  endfunction\n"
      "  function int h(u_t a);\n"
      "    return a.Other;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    z = g(tagged Small 8'hAB);\n"
      "    w = h(tagged Other 32'h12345678);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.ToUint64(), 0xABABu);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.ToUint64(), 0x12345678u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 6, "11.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 9, "11.9"));
}

TEST(TaggedUnionEval, TaggedPatternActualIsPlacedByMemberPosition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  typedef union tagged { void None; pair_t Add; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t u);\n"
      "    return u.Add.a * 10 + u.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{8'd1, 8'd2});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 6, "11.9"));
}

TEST(TaggedUnionEval, TaggedPatternActualIsPlacedByMemberName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  typedef union tagged { void None; pair_t Add; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t u);\n"
      "    return u.Add.a * 10 + u.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{b: 2, a: 1});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
}

TEST(TaggedUnionEval, TaggedExprActualBindsAnInlineUnionFormalsLayout) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  function int f(union tagged { void Invalid; int Valid; } a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial x = f(tagged Valid 5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 4, "11.9"));
}

TEST(TaggedUnionEval, TaggedExprActualOfInlineUnionFormalIsCheckedInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int y;\n"
      "  function int f(union tagged { void Invalid; int Valid; } a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial y = f(tagged Invalid);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 4, "11.9"));
}

TEST(TaggedUnionEval,
     TaggedPatternActualOfInlineUnionFormalReadsANestedTypedefMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  int x;\n"
      "  function int f(union tagged { void None; pair_t Add; } a);\n"
      "    return a.Add.a * 10 + a.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{3, 4});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 34u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 5, "11.9"));
}

TEST(TaggedUnionEval, CallResultActualCarriesTheReturnedTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int x;\n"
      "  function u_t g();\n"
      "    return tagged Valid (-7);\n"
      "  endfunction\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial x = f(g());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
}

TEST(TaggedUnionEval, CallResultActualOfVoidMemberIsCheckedInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int y;\n"
      "  function u_t h();\n"
      "    return tagged Invalid;\n"
      "  endfunction\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial y = f(h());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 8, "11.9"));
}

}  // namespace
