// Annex A.8.7: Numbers


#include <cstring>

#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

static double ToDouble(const Variable* var) {
  uint64_t bits = var->value.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

namespace {

// § integral_number — octal_number
TEST(SimA87, OctalNumber) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'o77;\n"
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

// § size — 1-bit literal
TEST(SimA87, Size1Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 1'b1;\n"
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

// § real_number — fixed_point_number simulates
TEST(SimA87, FixedPointNumber) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 2.718;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 2.718);
}

// § hex_digit — lowercase a-f
TEST(SimA87, HexDigitLowercase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'habcdef;\n"
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

// § binary_digit — x in binary
TEST(SimA87, BinaryXDigit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b10x0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Bit 1 is x: aval bit 1 and bval bit 1 set
  uint64_t bval = var->value.words[0].bval;
  EXPECT_NE(bval & 0x2u, 0u);
}

}  // namespace
