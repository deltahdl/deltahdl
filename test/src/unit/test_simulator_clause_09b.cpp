// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 16. always_comb with ternary operator: true condition.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombTernaryTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = sel ? a : b;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "    sel = 1;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xCAu);
}

// ---------------------------------------------------------------------------
// 17. always_comb with reduction AND.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always_comb y = &a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
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
  // &8'hFF = 1 (all bits set).
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 18. always_comb with reduction OR.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombReductionOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always_comb y = |a;\n"
      "  initial begin\n"
      "    a = 8'h01;\n"
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
  // |8'h01 = 1 (at least one bit set).
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 19. always_comb re-triggers when input changes.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombRetriggersOnChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, y;\n"
      "  always_comb y = a + 1;\n"
      "  initial begin\n"
      "    a = 10;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

// ---------------------------------------------------------------------------
// 20. always_comb with multi-bit addition (16-bit).
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombMultiBitAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always_comb y = a + b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'h4321;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

// ---------------------------------------------------------------------------
// 21. always_comb with begin-end block and multiple outputs.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombBlockMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "    diff = a - b;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'h20;\n"
      "    b = 8'h05;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* sum = f.ctx.FindVariable("sum");
  auto* diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x25u);
  EXPECT_EQ(diff->value.ToUint64(), 0x1Bu);
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
// 24. always_comb with comparison operator (greater-than).
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    if (a > b) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'h50;\n"
      "    b = 8'h30;\n"
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
  // a > b is true, so y = a = 0x50.
  EXPECT_EQ(y->value.ToUint64(), 0x50u);
}

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
