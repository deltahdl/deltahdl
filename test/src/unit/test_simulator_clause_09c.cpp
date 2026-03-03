// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 28. Verify .width on always_latch output with 1-bit result.
TEST(SimCh9c, WidthVerificationSingleBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 1;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 1u);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

// =============================================================================
// §9.2.3: Verify .width and .ToUint64() on results
// =============================================================================
// 29. 32-bit always_latch output verifies width and value.
TEST(SimCh9c, Width32BitAndToUint64) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [31:0] d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 32'hDEADBEEF;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 32u);
  EXPECT_EQ(q->value.ToUint64(), 0xDEADBEEFu);
}

// 30. always_latch with begin/end block and arithmetic on RHS.
TEST(SimCh9c, BeginEndBlockWithArithmetic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en) q = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 8u);
  // 0x10 + 0x20 = 0x30.
  EXPECT_EQ(q->value.ToUint64(), 0x30u);
}

}  // namespace
