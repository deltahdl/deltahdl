#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
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
  // A two-state object yields 0 (not x) for an out-of-bounds bit-select.
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
  // An unknown index on a two-state object yields 0 (not x).
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[0+:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[7-:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ExpressionSim, IndexedPartSelectRuntimeVaryingBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // The base of an indexed part-select is evaluated at run time: sel==4
  // selects bits [7:4] of 0xABCD, which is 0xC.
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, BitSelectOfConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[6];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // A concatenation is a valid operand for a bit-select: {a,b} is 8'b1100_0011,
  // and bit 6 (the next-to-top bit, contributed by a) is 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, PartSelectOfConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[7:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // A concatenation is a valid operand for a part-select: bits [7:4] of
  // {a,b} == 8'b1100_0011 select a, which is 4'b1100 (0xC).
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(PrimarySim, PrimaryBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial begin data = 8'b10101010; x = data[1]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LvalueSim, VarLvalueBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[3] = 1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[8+:8] = 8'hAB; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[15-:8] = 8'hCD; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

}  // namespace
TEST(BlockingAssignBitSelect, BlockingAssignBitSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("bs", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bs");
  sel->index = MakeInt(f.arena, 3);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(BlockingAssignPartSelect, BlockingAssignPartSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("ps", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x0F);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ps");
  sel->index = MakeInt(f.arena, 7);
  sel->index_end = MakeInt(f.arena, 4);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 0xA);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAFu);
}

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
