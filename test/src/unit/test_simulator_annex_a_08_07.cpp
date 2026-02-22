// Tests for A.8.7 — Numbers — Simulation

#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA87Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA87Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static double ToDouble(const Variable *var) {
  uint64_t bits = var->value.ToUint64();
  double d;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

}  // namespace

// =============================================================================
// A.8.7 Numbers — Simulation
// =============================================================================

// § number — integral_number simulates

TEST(SimA87, NumberIntegral) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// § number — real_number simulates

TEST(SimA87, NumberReal) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 3.14);
}

// § integral_number — decimal_number (unsized)

TEST(SimA87, DecimalUnsized) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 255u);
}

// § integral_number — binary_number

TEST(SimA87, BinaryNumber) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b10101010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// § integral_number — octal_number

TEST(SimA87, OctalNumber) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'o77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

// § integral_number — hex_number

TEST(SimA87, HexNumber) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// § decimal_number — [size] decimal_base unsigned_number

TEST(SimA87, DecimalSizedBase) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

// § decimal_number — [size] decimal_base x_digit (all x)

TEST(SimA87, DecimalXDigitAllBits) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x fills all bits — check bval is set (four-state x)
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// § decimal_number — [size] decimal_base z_digit (all z)

TEST(SimA87, DecimalZDigitAllBits) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // z: aval=0, bval=set
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// § size — 1-bit literal

TEST(SimA87, Size1Bit) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § size — 16-bit literal

TEST(SimA87, Size16Bit) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
}

// § real_number — fixed_point_number simulates

TEST(SimA87, FixedPointNumber) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 2.718;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 2.718);
}

// § real_number — scientific notation simulates

TEST(SimA87, ScientificNotation) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.5e3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 1500.0);
}

// § real_number — scientific with positive exponent

TEST(SimA87, ScientificPositiveExp) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.0e+2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 100.0);
}

// § real_number — scientific with negative exponent

TEST(SimA87, ScientificNegativeExp) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.0e-2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 0.01);
}

// § exp — uppercase E

TEST(SimA87, ExpUppercase) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 2.5E2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 250.0);
}

// § unsigned_number — with underscores

TEST(SimA87, UnsignedNumberUnderscores) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1000u);
}

// § binary_value — with underscores

TEST(SimA87, BinaryValueUnderscores) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b1010_1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// § octal_value — with underscores

TEST(SimA87, OctalValueUnderscores) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 12'o77_77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 07777u);
}

// § hex_value — with underscores

TEST(SimA87, HexValueUnderscores) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hAB_CD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// § decimal_base — 'D (uppercase)

TEST(SimA87, DecimalBaseUpper) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'D99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// § binary_base — 'B (uppercase)

TEST(SimA87, BinaryBaseUpper) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'B1111;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

// § octal_base — 'O (uppercase)

TEST(SimA87, OctalBaseUpper) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'O77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

// § hex_base — 'H (uppercase)

TEST(SimA87, HexBaseUpper) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'HAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § signed bases — 'sd simulates

TEST(SimA87, SignedDecimal) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'sd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// § signed bases — 'sb simulates

TEST(SimA87, SignedBinary) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'sb1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// § signed bases — 'sh simulates

TEST(SimA87, SignedHex) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'shAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § x_digit — hex x fills 4 bits

TEST(SimA87, XDigitInHex) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Low nibble is x: aval bits 0-3 set, bval bits 0-3 set
  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0xFu);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

// § z_digit — hex z fills 4 bits

TEST(SimA87, ZDigitInHex) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Low nibble is z: aval bits 0-3 clear, bval bits 0-3 set
  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0x0u);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

// § z_digit — ? synonym for z in binary

TEST(SimA87, QuestionMarkAsZ) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b0?0?;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // bits 0 and 2 are z: bval has those bits set
  uint64_t bval = var->value.words[0].bval;
  EXPECT_NE(bval & 0x5u, 0u);
}

// § unbased_unsized_literal — '0

TEST(SimA87, UnbasedUnsizedZero) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unbased_unsized_literal — '1

TEST(SimA87, UnbasedUnsizedOne) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xFFu);
}

// § unbased_unsized_literal — 'x (fills all bits with x)

TEST(SimA87, UnbasedUnsizedX) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x: both aval and bval set
  EXPECT_NE(var->value.words[0].aval, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// § unbased_unsized_literal — 'z (fills all bits with z)

TEST(SimA87, UnbasedUnsizedZ) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // z: aval=0, bval=set
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// § hex_digit — lowercase a-f

TEST(SimA87, HexDigitLowercase) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'habcdef;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

// § hex_digit — uppercase A-F

TEST(SimA87, HexDigitUppercase) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'hABCDEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

// § binary_digit — x in binary

TEST(SimA87, BinaryXDigit) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b10x0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Bit 1 is x: aval bit 1 and bval bit 1 set
  uint64_t bval = var->value.words[0].bval;
  EXPECT_NE(bval & 0x2u, 0u);
}

// § octal_digit — all octal digits

TEST(SimA87, OctalDigitAll) {
  SimA87Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'o01234567;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 01234567u);
}
