// §11.4.10: Shift operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ConstEval, Shifts) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 << 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >> 2", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 <<< 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >>> 2", f)), 4);
}

// § binary_operator — shift operators elaborate
TEST(ElabA86, BinaryArithShiftRightElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd128 >>> 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryArithShiftLeftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 <<< 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ---------------------------------------------------------------------------
// 13. Bit-select in always_comb using initial begin/end.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'b0000_0100;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a = 4, a >> 2 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 15. Upper part-select via shift in always_comb (upper nibble).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombUpperPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a >> 4) & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// ---------------------------------------------------------------------------
// 26. always_comb with shift operations.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'b0000_0011;\n"
      "  always_comb begin\n"
      "    result = a << 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 22. always_comb with left shift.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombLeftShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, y;\n"
      "  always_comb y = data << 2;\n"
      "  initial begin\n"
      "    data = 8'h0F;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x0F << 2 = 0x3C.
  EXPECT_EQ(y->value.ToUint64(), 0x3Cu);
}

// ---------------------------------------------------------------------------
// 23. always_comb with right shift.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombRightShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, y;\n"
      "  always_comb y = data >> 4;\n"
      "  initial begin\n"
      "    data = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0xF0 >> 4 = 0x0F.
  EXPECT_EQ(y->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// 19. Blocking assignment with shift operators (<<, >>).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignShiftOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] r_shl, r_shr;\n"
      "  initial begin\n"
      "    a = 8'h0F;\n"
      "    r_shl = a << 2;\n"
      "    r_shr = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* shl = f.ctx.FindVariable("r_shl");
  auto* shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(shl, nullptr);
  ASSERT_NE(shr, nullptr);
  // 0x0F << 2 = 0x3C (8-bit)
  EXPECT_EQ(shl->value.ToUint64(), 0x3Cu);
  // 0x0F >> 2 = 0x03
  EXPECT_EQ(shr->value.ToUint64(), 0x03u);
}

}  // namespace
