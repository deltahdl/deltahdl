#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(ExpressionSim, PartSelectWriteKeepsTheTargetBitsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[3:0] = 4'h0;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(96, '1') + "0000");
}

TEST(ExpressionSim, BitSelectWriteKeepsTheTargetBitsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[0] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(99, '1') + "0");
}

TEST(ExpressionSim, PartSelectWriteKeepsTheTargetsUnknownBitsOutsideTheWindow) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hxx;\n"
      "    a[1:0] = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "xxxxxx11");
}

TEST(ExpressionSim, BitSelectWriteKeepsTheTargetsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hxx;\n"
      "    a[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "xxxxxxx1");
}

TEST(ExpressionSim, PartSelectWriteCarriesAnUnknownBitOfTheValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[1:0] = 2'b1x;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "0000001x");
}

TEST(ExpressionSim, BitSelectWriteCarriesAnUnknownValueBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    a[0] = 1'bx;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1111111x");
}

TEST(SelectBoundaryBehavior, PartSelectWriteLandsAtAnOffsetAboveTheFirstWord) {
  SimFixture f;
  auto* var = MakeVar(f, "wop", 100, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "wop");
  sel->index = MakeInt(f.arena, 71);
  sel->index_end = MakeInt(f.arena, 68);

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval & 0xF0u, 0xF0u);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(SelectBoundaryBehavior, BitSelectWriteLandsAtAnOffsetAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [64:0] enable;\n"
      "  initial begin\n"
      "    enable = 0;\n"
      "    enable[64] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "enable");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 1u);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(ExpressionSim, PartSelectWriteAboveTheFirstWordCarriesUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[71:68] = 4'b10x1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(),
            std::string(28, '1') + "10x1" + std::string(68, '1'));
}

TEST(SelectBoundaryBehavior, PackedElementWriteAgreesWithItsStorageBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] p;\n"
      "  initial begin\n"
      "    p = 32'h0;\n"
      "    p[2] = 8'hA5;\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  auto* elem = f.arena.Create<Expr>();
  elem->kind = ExprKind::kSelect;
  elem->base = MakeId(f.arena, "p");
  elem->index = MakeInt(f.arena, 2);
  auto bits = SelectStorageBits(*var, elem, f.ctx, f.arena);
  EXPECT_EQ(bits.lo, 16u);
  EXPECT_EQ(bits.width, 8u);

  auto stored = var->value.ToUint64();
  EXPECT_EQ(stored, uint64_t{0x00A50000});
  auto window = ((uint64_t{1} << bits.width) - 1) << bits.lo;
  EXPECT_EQ(stored & window, uint64_t{0xA5} << bits.lo);
  EXPECT_EQ(stored & ~window, uint64_t{0});
}

TEST(SelectBoundaryBehavior, BitSelectWriteTakesAnAscendingDeclarationsBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:7] asc;\n"
      "  initial begin\n"
      "    asc = 8'h00;\n"
      "    asc[6] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "asc");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), uint64_t{0x02});
}

TEST(SelectBoundaryBehavior, PartSelectWithAnUnknownWidthBoundWritesNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] tgt;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    tgt = 8'hC3;\n"
      "    w = 4'bxxxx;\n"
      "    tgt[0 +: w] = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f, "tgt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), uint64_t{0xC3});
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 7, "11.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 7,
                            "11.5.1"));
}

TEST(SelectBoundaryBehavior, BitSelectOfAnUnknownBitAgreesWithThePartSelect) {
  SimFixture f;
  auto* bit_sel = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic bit_sel;\n"
      "  logic part_sel;\n"
      "  initial begin\n"
      "    a = 8'bxxxxxxxx;\n"
      "    bit_sel = a[0];\n"
      "    part_sel = a[0:0];\n"
      "  end\n"
      "endmodule\n",
      f, "bit_sel");
  ASSERT_NE(bit_sel, nullptr);
  auto* part_sel = f.ctx.FindVariable("part_sel");
  ASSERT_NE(part_sel, nullptr);
  EXPECT_EQ(part_sel->value.ToString(), "x");
  EXPECT_EQ(bit_sel->value.ToString(), "x");
  EXPECT_EQ(bit_sel->value.ToString(), part_sel->value.ToString());
}

TEST(SelectBoundaryBehavior, BitSelectOfAHighImpedanceBitReturnsZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic bit_sel;\n"
      "  initial begin\n"
      "    a = 8'bzzzzzzzz;\n"
      "    bit_sel = a[0];\n"
      "  end\n"
      "endmodule\n",
      f, "bit_sel");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "z");
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(SelectBoundaryBehavior, BitSelectAboveTheFirstWordReadsThatWordsBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  initial begin\n"
      "    w = 100'h1_0000_0000_0000_0000;\n"
      "    hi = w[64];\n"
      "    lo = w[0];\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{1});
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0});

  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToString(), "1");
  EXPECT_EQ(lo->value.ToString(), "0");
}

TEST(SelectBoundaryBehavior, PartSelectHighOverhangAboveTheFirstWordReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [70:0] r;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    r = a[70:0];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{0x7F});
  EXPECT_EQ(var->value.words[1].bval, uint64_t{0x7F});
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0xFFFFFFFFFFFFFFA5});
  EXPECT_EQ(var->value.words[0].bval, uint64_t{0xFFFFFFFFFFFFFF00});
}

TEST(SelectBoundaryBehavior, PartSelectLowOverhangAboveTheFirstWordReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [79:0] r;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    r = a[7 -: 80];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10100101" + std::string(72, 'x'));
}

TEST(ExpressionSim, PartSelectWriteToAClassPropertyLandsInIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    logic [15:0] p;\n"
      "  endclass\n"
      "  logic [15:0] r;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    c.p[7:0] = 8'h00;\n"
      "    r = c.p;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAA00u);
}

TEST(ExpressionSim, BitSelectWriteToAClassPropertyLandsInIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    logic [15:0] p;\n"
      "  endclass\n"
      "  logic [15:0] r;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'h00FF;\n"
      "    c.p[8] = 1'b1;\n"
      "    r = c.p;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01FFu);
}

TEST(ExpressionSim, PartSelectWriteToAClassPropertyLeavesItsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    logic [15:0] p;\n"
      "  endclass\n"
      "  logic [15:0] r;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAAxB;\n"
      "    c.p[3:0] = 4'hF;\n"
      "    r = c.p;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10101010xxxx1111");
}

TEST(SelectXZHandling,
     NonIndexedPartSelectWithAnUnknownFirstBoundSpansIndices) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("nipsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xA5);
  MakeVar4(f, "nipsi", 4, 0, 1);

  auto* wide = f.arena.Create<Expr>();
  wide->kind = ExprKind::kSelect;
  wide->base = MakeId(f.arena, "nipsv");
  wide->index = MakeId(f.arena, "nipsi");
  wide->index_end = MakeInt(f.arena, 4);
  auto wide_result = EvalExpr(wide, f.ctx, f.arena);
  EXPECT_EQ(wide_result.width, 4u);
  EXPECT_EQ(wide_result.ToString(), "xxxx");

  auto* narrow = f.arena.Create<Expr>();
  narrow->kind = ExprKind::kSelect;
  narrow->base = MakeId(f.arena, "nipsv");
  narrow->index = MakeId(f.arena, "nipsi");
  narrow->index_end = MakeInt(f.arena, 6);
  auto narrow_result = EvalExpr(narrow, f.ctx, f.arena);
  EXPECT_EQ(narrow_result.width, 2u);
  EXPECT_EQ(narrow_result.ToString(), "xx");
}

TEST(SelectXZHandling, NonIndexedPartSelectWithAnUnknownFirstBoundReadsAllX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] r;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    r = a[1'bx : -2];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxx");
}

TEST(SelectXZHandling, IndexedPartSelectWithAnUnknownBaseKeepsItsWidth) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("ipsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xA5);
  MakeVar4(f, "ipsi", 4, 0, 1);

  auto* up = f.arena.Create<Expr>();
  up->kind = ExprKind::kSelect;
  up->base = MakeId(f.arena, "ipsv");
  up->index = MakeId(f.arena, "ipsi");
  up->index_end = MakeInt(f.arena, 4);
  up->is_part_select_plus = true;
  auto up_result = EvalExpr(up, f.ctx, f.arena);
  EXPECT_EQ(up_result.width, 4u);
  EXPECT_EQ(up_result.ToString(), "xxxx");

  auto* down = f.arena.Create<Expr>();
  down->kind = ExprKind::kSelect;
  down->base = MakeId(f.arena, "ipsv");
  down->index = MakeId(f.arena, "ipsi");
  down->index_end = MakeInt(f.arena, 4);
  down->is_part_select_minus = true;
  auto down_result = EvalExpr(down, f.ctx, f.arena);
  EXPECT_EQ(down_result.width, 4u);
  EXPECT_EQ(down_result.ToString(), "xxxx");
}

}  // namespace
