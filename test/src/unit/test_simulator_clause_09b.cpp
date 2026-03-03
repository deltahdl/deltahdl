// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 25. always_comb with equality comparison.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombEqualityCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic y;\n"
      "  always_comb y = (a == b);\n"
      "  initial begin\n"
      "    a = 8'h42;\n"
      "    b = 8'h42;\n"
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
  // a == b is true -> y = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 26. always_comb sensitivity: changes signal 'a', observes result.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombSensitivityRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  // Sensitivity map should have signal 'a' mapped.
  const auto& procs = f.ctx.GetSensitiveProcesses("a");
  EXPECT_FALSE(procs.empty());
}

// ---------------------------------------------------------------------------
// 27. always_comb with subtraction.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombSubtraction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a - b;\n"
      "  initial begin\n"
      "    a = 8'h50;\n"
      "    b = 8'h10;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0x40u);
}

// ---------------------------------------------------------------------------
// 28. always_comb with multiplication.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always_comb y = a * b;\n"
      "  initial begin\n"
      "    a = 16'd7;\n"
      "    b = 16'd6;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 42u);
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

// ---------------------------------------------------------------------------
// 30. always_comb with chained combinational logic: a XOR b, then OR c.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombChainedLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always_comb y = (a ^ b) | c;\n"
      "  initial begin\n"
      "    a = 8'hA0;\n"
      "    b = 8'h50;\n"
      "    c = 8'h0F;\n"
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
  // (0xA0 ^ 0x50) | 0x0F = 0xF0 | 0x0F = 0xFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

}  // namespace
