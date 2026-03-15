// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static bool RunSim(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

TEST(IntegerLiteralSim, PrimaryIntegerLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hAB;\n"
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

TEST(IntegerLiteralSim, PrimaryUnbasedUnsized1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(IntegerLiteralSim, PrimaryUnbasedUnsized0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IntegerLiteralSim, PrimaryHexLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(IntegerLiteralSim, PrimaryBinaryLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b11001100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCu);
}

TEST(IntegerLiteralSim, NumberIntegral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IntegerLiteralSim, DecimalUnsized) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 255u);
}

TEST(IntegerLiteralSim, BinaryNumber) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b10101010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(IntegerLiteralSim, HexNumber) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(IntegerLiteralSim, DecimalSizedBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

TEST(IntegerLiteralSim, DecimalZDigitAllBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, Size16Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
}

TEST(IntegerLiteralSim, UnsignedNumberUnderscores) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1000u);
}

TEST(IntegerLiteralSim, BinaryValueUnderscores) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b1010_1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(IntegerLiteralSim, DecimalBaseUpper) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'D99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IntegerLiteralSim, BinaryBaseUpper) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'B1111;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

TEST(IntegerLiteralSim, OctalBaseUpper) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'O77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

TEST(IntegerLiteralSim, HexBaseUpper) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'HAB;\n"
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

TEST(IntegerLiteralSim, SignedDecimal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'sd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IntegerLiteralSim, SignedBinary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'sb1010;\n"
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

TEST(IntegerLiteralSim, SignedHex) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'shAB;\n"
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

TEST(IntegerLiteralSim, XDigitInHex) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0xFu);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

TEST(IntegerLiteralSim, ZDigitInHex) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0x0u);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

TEST(IntegerLiteralSim, QuestionMarkAsZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b0?0?;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  uint64_t bval = var->value.words[0].bval;
  EXPECT_NE(bval & 0x5u, 0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].aval, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, HexDigitUppercase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'hABCDEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

TEST(IntegerLiteralSim, SimpleDecimalNumber) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 659;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 659u);
}

TEST(IntegerLiteralSim, SizedBinaryLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b1001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 9u);
}

TEST(IntegerLiteralSim, SizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 12'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, SizedDecimalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

TEST(IntegerLiteralSim, UnsizedHexLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(IntegerLiteralSim, UnsizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, UnaryMinusBeforeSize) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd6;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 250u);
}

TEST(IntegerLiteralSim, NegativeTwosComplement) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 255u);
}

TEST(IntegerLiteralSim, TruncationFromLeft) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b11001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x09u);
}

TEST(IntegerLiteralSim, SignedBasedLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  uint32_t mask = 0xFFFFFFFF;
  EXPECT_EQ(result & mask, mask);
}

TEST(IntegerLiteralSim, SizeConstantNonzero) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, NumberIntegralDecimal) {
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 100;\nendmodule\n", "x");
  EXPECT_EQ(v, 100u);
}

TEST(IntegerLiteralSim, NumberIntegralBinary) {
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'b1010_0101;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xA5u);
}

TEST(IntegerLiteralSim, NumberIntegralOctal) {
  auto v = RunAndGet(
      "module t;\n  logic [11:0] x;\n  initial x = 12'o7654;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 07654u);
}

TEST(IntegerLiteralSim, NumberIntegralHex) {
  auto v = RunAndGet(
      "module t;\n  logic [15:0] x;\n  initial x = 16'hCAFE;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xCAFEu);
}

TEST(IntegerLiteralSim, NumberAllIntegralBases) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [7:0] a, b, c, d;\n"
                     "  initial begin\n"
                     "    a = 255;\n"
                     "    b = 8'hFF;\n"
                     "    c = 8'o377;\n"
                     "    d = 8'b1111_1111;\n"
                     "  end\n"
                     "endmodule\n"));
  const char* const kNames[] = {"a", "b", "c", "d"};
  for (const char* name : kNames) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 255u) << name;
  }
}

TEST(IntegerLiteralSim, NumberAsPrimaryLiteralInTernary) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd99 : 8'd0;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 99u);
}

TEST(IntegerLiteralSim, NumberSizedDecimalBase) {
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'd200;\nendmodule\n", "x");
  EXPECT_EQ(v, 200u);
}

TEST(IntegerLiteralSim, NumberUnderscoreInIntegral) {
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 1_000_000;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 1000000u);
}

TEST(IntegerLiteralSim, OctalZDigitFillsThreeBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o0z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x07, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

TEST(IntegerLiteralSim, BinaryZDigitFillsOneBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b010z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x1, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0x1, 0x1u);
}

TEST(IntegerLiteralSim, LeftPadZWhenLeftmostIsZ) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hz5;\n"
      "endmodule\n",
      "x");
  // z digits pad with z from left — low nibble should be 5 (known)
  // but top nibble is z so aval top bits = 0, bval top bits = F
  // RunAndGet only returns aval, so value should reflect just known bits
  // x is 8'hz5 => top 4 bits z, bottom 4 bits 0101 => aval=0x05
  EXPECT_EQ(result & 0x0Fu, 0x05u);
}

TEST(IntegerLiteralSim, UnsizedDefaultWidth32Bits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'hFFFF_FFFF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, SignedOctal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'so77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

TEST(IntegerLiteralSim, XDigitInBinary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b1x01;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x4, 0x4u);
  EXPECT_EQ(var->value.words[0].bval & 0x4, 0x4u);
}

TEST(IntegerLiteralSim, XDigitInOctal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o0x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x07, 0x07u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

TEST(IntegerLiteralSim, DecimalXDigitFillsAllBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint8_t mask = 0xFF;
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

}  // namespace
