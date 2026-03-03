// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 35. Left padding: known value (0x3x -> yields 03x)
// ---------------------------------------------------------------------------
TEST(SimCh50701, LeftPadKnownHex) {
  // §5.7.1: Known value with x in low nibble — yields 03x.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'h3x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x: aval=1, bval=1. Lower nibble = x, middle = 3, upper = 0-pad.
  EXPECT_EQ(var->value.words[0].aval & 0xFFF, 0x03Fu);
  EXPECT_EQ(var->value.words[0].bval & 0x00F, 0x00Fu);
  EXPECT_EQ(var->value.words[0].bval & 0xF00, 0x000u);
}

// ---------------------------------------------------------------------------
// 36. Decimal single-digit x
// ---------------------------------------------------------------------------
TEST(SimCh50701, DecimalSingleDigitX) {
  // §5.7.1: Decimal literal allows single x/z/? digit only.
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

// ---------------------------------------------------------------------------
// 37. Size constant must be nonzero
// ---------------------------------------------------------------------------
TEST(SimCh50701, SizeConstantNonzero) {
  // §5.7.1: Size constant must be nonzero.
  // Using size=1 (the smallest legal size) verifies nonzero is accepted.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

}  // namespace
