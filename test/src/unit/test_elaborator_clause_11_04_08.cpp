// §11.4.8: Bitwise operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Bitwise) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 & 10", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 | 3", f)), 15);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 ^ 3", f)), 6);
}

// § expression — unary operator in initial elaborates
TEST(ElabA83, UnaryExprInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, UnaryBitwiseNotElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § binary_operator — bitwise operators elaborate
TEST(ElabA86, BinaryBitwiseXnorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF ^~ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ---------------------------------------------------------------------------
// 14. Part-select via mask in always_comb (lower nibble).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// ---------------------------------------------------------------------------
// 29. always_comb with NAND expression (~(a & b)), masked to width.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombNand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = ~(a & b);\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h0F;\n"
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
  // ~(0xFF & 0x0F) = ~0x0F = 0xF0 in the low 8 bits.
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0xF0u);
}

}  // namespace
