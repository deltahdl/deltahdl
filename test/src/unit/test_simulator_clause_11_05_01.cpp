#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(EvalAdv, PartSelectPartialOOB) {
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

TEST(EvalAdv, ArrayXZAddrReturnsX) {
  SimFixture f;

  MakeVar(f, "arr4[0]", 8, 0x11);
  MakeVar(f, "arr4[1]", 8, 0x22);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr4", info);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "arr4");

  auto* idx = MakeInt(f.arena, 0);
  sel->index = idx;

  auto* xvar = f.ctx.CreateVariable("xidx", 8);
  xvar->value = MakeLogic4Vec(f.arena, 8);
  xvar->value.words[0].aval = 1;
  xvar->value.words[0].bval = 1;
  sel->index = MakeId(f.arena, "xidx");

  auto result = EvalExpr(sel, f.ctx, f.arena);

  EXPECT_NE(result.nwords, 0u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, BitSelectXAddr) {
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

TEST(EvalOpXZ, PartSelectXAddr) {
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

TEST(SimA83, PartSelectRange) {
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

TEST(SimA83, IndexedPartSelectPlus) {
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

TEST(SimA83, IndexedPartSelectMinus) {
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

TEST(SimA84, PrimaryBitSelect) {
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

TEST(SimA84, PrimaryPartSelectRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[15:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SimA84, PrimaryIndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[8+:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SimA84, PrimaryIndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[15-:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SimA85, VarLvalueBitSelect) {
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

TEST(SimA85, VarLvalueIndexedPartSelectPlus) {
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

TEST(SimA85, VarLvalueIndexedPartSelectMinus) {
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

}
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

