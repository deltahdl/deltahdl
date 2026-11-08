#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(SelectBoundaryBehavior, PartSelectPartialOOB) {
  SimFixture f;

  MakeVar(f, "ov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ov");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);

  EXPECT_EQ(result.words[0].aval & 0x3u, 0x3u);

  EXPECT_NE(result.words[0].bval & 0xCu, 0u);
}

TEST(SelectBoundaryBehavior, BitSelectOOBReturnsX) {
  SimFixture f;
  MakeVar(f, "bov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bov");
  sel->index = MakeInt(f.arena, 10);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SelectBoundaryBehavior, PartSelectCompletelyOOBReturnsX) {
  SimFixture f;
  MakeVar(f, "cov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "cov");
  sel->index = MakeInt(f.arena, 12);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0xFu);
}

TEST(SelectBoundaryBehavior, TwoStateBitSelectOOBReturnsZero) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("tsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  v->is_4state = false;
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "tsv");
  sel->index = MakeInt(f.arena, 10);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.words[0].bval & 1u, 0u);
  EXPECT_EQ(result.words[0].aval & 1u, 0u);
}

TEST(SelectXZHandling, TwoStateBitSelectXZIndexReturnsZero) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("tsx", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  v->is_4state = false;
  MakeVar4(f, "tsi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "tsx");
  sel->index = MakeId(f.arena, "tsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.words[0].bval & 1u, 0u);
  EXPECT_EQ(result.words[0].aval & 1u, 0u);
}

TEST(SelectXZHandling, BitSelectXAddr) {
  SimFixture f;

  auto* v = f.ctx.CreateVariable("bsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "bsi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bsv");
  sel->index = MakeId(f.arena, "bsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SelectXZHandling, PartSelectXAddr) {
  SimFixture f;

  auto* v = f.ctx.CreateVariable("psv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "psi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "psv");
  sel->index = MakeId(f.arena, "psi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(ExpressionSim, PartSelectRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[3:0];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectPlus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[0+:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[7-:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ExpressionSim, IndexedPartSelectRuntimeVaryingBase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [3:0] sel;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    sel = 4;\n"
      "    x = data[sel +: 4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, BitSelectOfConcatenation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[6];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, PartSelectOfConcatenation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[7:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, PackedStructBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic x;\n"
      "  initial begin s = 8'hC3; x = s[0]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, PackedStructPartSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic [3:0] x;\n"
      "  initial begin s = 8'hC3; x = s[7:4]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, ParameterBitAndPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter [15:0] P = 16'hABCD;\n"
      "  logic pb;\n"
      "  logic [7:0] phi;\n"
      "  initial begin pb = P[0]; phi = P[15:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* pb = f.ctx.FindVariable("pb");
  auto* phi = f.ctx.FindVariable("phi");
  ASSERT_NE(pb, nullptr);
  ASSERT_NE(phi, nullptr);
  EXPECT_EQ(pb->value.ToUint64(), 1u);
  EXPECT_EQ(phi->value.ToUint64(), 0xABu);
}

TEST(PrimarySim, PrimaryBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial begin data = 8'b10101010; x = data[1]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LvalueSim, VarLvalueBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[3] = 1; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectPlus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[8+:8] = 8'hAB; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[15-:8] = 8'hCD; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

void ExpectSelectOfFourStateReadsX(const char* src) {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

void ExpectSelectOfTwoStateReadsZero(const char* src) {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
}

TEST(ExpressionSim, BitSelectOutOfBoundsFourStateReadsX) {
  ExpectSelectOfFourStateReadsX(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; r = d[10]; end\n"
      "endmodule\n");
}

TEST(ExpressionSim, BitSelectOutOfBoundsTwoStateReadsZero) {
  ExpectSelectOfTwoStateReadsZero(
      "module t;\n"
      "  bit [7:0] d;\n"
      "  bit r;\n"
      "  initial begin d = 8'hFF; r = d[10]; end\n"
      "endmodule\n");
}

TEST(ExpressionSim, BitSelectUnknownIndexFourStateReadsX) {
  ExpectSelectOfFourStateReadsX(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] i;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; i = 4'bxxxx; r = d[i]; end\n"
      "endmodule\n");
}

TEST(ExpressionSim, BitSelectUnknownIndexTwoStateReadsZero) {
  ExpectSelectOfTwoStateReadsZero(
      "module t;\n"
      "  bit [7:0] d;\n"
      "  logic [3:0] i;\n"
      "  bit r;\n"
      "  initial begin d = 8'hFF; i = 4'bxxxx; r = d[i]; end\n"
      "endmodule\n");
}

TEST(ExpressionSim, PartSelectCompletelyOutOfBoundsReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] r;\n"
      "  initial begin d = 8'hA5; r = d[13:10]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0xFu);
}

TEST(ExpressionSim, PartSelectPartiallyOutOfBoundsReadsXForOutOfRangeBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] r;\n"
      "  initial begin d = 8'hA5; r = d[9:6]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0xCu, 0xCu);
  EXPECT_EQ(var->value.words[0].bval & 0x3u, 0u);
  EXPECT_EQ(var->value.words[0].aval & 0x3u, 0x2u);
}

TEST(ExpressionSim, BitSelectOutOfBoundsWriteHasNoEffect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'hAB; d[10] = 1'b1; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ExpressionSim, PartSelectPartiallyOutOfBoundsWriteAffectsInRangeOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'h00; d[9:6] = 4'hF; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC0u);
}

TEST(ExpressionSim, PartSelectRunningOffLowEndWritesItsOwnHighBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[1 -: 4] = 4'b1101; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
}

TEST(ExpressionSim, PartSelectRunningOffBothEndsWritesItsMiddleBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[9 -: 12] = 12'hABC; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAFu);
}

TEST(ExpressionSim, PartSelectRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[9:6] = 4'b1101; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x40u);
}

TEST(ExpressionSim, NonIndexedPartSelectBelowLowBoundWritesInRangeBitsOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'h00; b = 8'h00;\n"
      "    a[1:-2] = 4'b1101; b[1 -: 4] = 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  auto* indexed = f.ctx.FindVariable("b");
  ASSERT_NE(indexed, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
  EXPECT_EQ(indexed->value.ToUint64(), var->value.ToUint64());
}

TEST(ExpressionSim, UnsignedPartSelectBoundKeepsItsTopBitAsMagnitude) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] u;\n"
      "  initial begin u = 16'h0000; u[4'hE : 4'hB] = 4'b1101; end\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6800u);
}

TEST(ExpressionSim, MultiDimPackedArrayBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] pa;\n"
      "  logic b;\n"
      "  initial begin pa = 32'h0000_0100; b = pa[1][0]; end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, ParameterNonIndexedPartSelectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter integer P = 7;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial begin data = 16'hA5A5; y = data[P:0]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(ExpressionSim, LocalparamNonIndexedPartSelectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam integer L = 7;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial begin data = 16'hA5A5; y = data[L:0]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(SelectBoundaryBehavior, ZeroWidthPartSelectWriteNames11_5_1) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zwp", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x5A);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "zwp");
  sel->index = MakeInt(f.arena, 2);
  sel->index_end = MakeInt(f.arena, 0);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0x3), f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 0,
                            "11.5.1"));
}

}  // namespace
TEST(SelectBoundaryBehavior, BitSelectOOBWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("bow", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bow");
  sel->index = MakeInt(f.arena, 10);

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 1, 1), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectBoundaryBehavior, PartSelectCompletelyOOBWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pow", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "pow");
  sel->index = MakeInt(f.arena, 12);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectBoundaryBehavior, PartSelectPartialOOBWriteInRangeOnly) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("ppw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ppw");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64() & 0xC0u, 0xC0u);
  EXPECT_EQ(var->value.ToUint64() & 0x3Fu, 0x00u);
}

TEST(SelectBoundaryBehavior, PartSelectPartialOOBLowEndSourceBits) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("plw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "plw");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_minus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xD), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
}

TEST(SelectBoundaryBehavior,
     NegativeNonIndexedBoundReadsXForItsOutOfRangeBits) {
  SimFixture f;

  MakeVar(f, "nrv", 8, 0xA5);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nrv");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 2));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);

  EXPECT_EQ(result.words[0].bval & 0x3u, 0x3u);

  EXPECT_EQ(result.words[0].bval & 0xCu, 0u);
  EXPECT_EQ(result.words[0].aval & 0xCu, 0x4u);
}

TEST(SelectBoundaryBehavior, NegativeNonIndexedBoundClampsToTheLowEnd) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("nlw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nlw");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 2));

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xD), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
}

TEST(SelectXZHandling, BitSelectXZIndexWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("bxw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* idx_var = f.ctx.CreateVariable("bxi", 4);
  idx_var->value = MakeLogic4Vec(f.arena, 4);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bxw");
  sel->index = MakeId(f.arena, "bxi");

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 1, 1), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectXZHandling, PartSelectXZIndexWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pxw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* idx_var = f.ctx.CreateVariable("pxi", 4);
  idx_var->value = MakeLogic4Vec(f.arena, 4);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "pxw");
  sel->index = MakeId(f.arena, "pxi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectSimulation, OutOfRangeSelectOfATwoStatePropertyIsZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    bit [7:0] two = 8'd13; logic [7:0] four = 8'd13;\n"
      "    function bit own(); return two[9]; endfunction\n"
      "  endclass\n"
      "  C h; int idx = 9;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%b %b %b %b\", h.two[9], h.two[idx], h.own(), "
      "h.four[9]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0 0 x\n");
}
