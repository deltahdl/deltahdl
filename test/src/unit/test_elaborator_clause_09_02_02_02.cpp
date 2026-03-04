// §9.2.2.2: Combinational logic always_comb procedure

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 10. Two always_comb blocks in the same module.
// ---------------------------------------------------------------------------
TEST(SimCh9, MultipleAlwaysCombBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  initial begin\n"
      "    a = 8'd15;\n"
      "    b = 8'd5;\n"
      "  end\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "  end\n"
      "  always_comb begin\n"
      "    diff = a - b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("sum");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 20u);
  auto* d = f.ctx.FindVariable("diff");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// 12. Multiple outputs from one always_comb block.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] doubled, incremented;\n"
      "  initial a = 8'd25;\n"
      "  always_comb begin\n"
      "    doubled = a << 1;\n"
      "    incremented = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* dbl = f.ctx.FindVariable("doubled");
  ASSERT_NE(dbl, nullptr);
  EXPECT_EQ(dbl->value.ToUint64(), 50u);
  auto* inc = f.ctx.FindVariable("incremented");
  ASSERT_NE(inc, nullptr);
  EXPECT_EQ(inc->value.ToUint64(), 26u);
}

// ---------------------------------------------------------------------------
// 28. always_comb with explicit zero inputs produces zero output.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombExplicitZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a | b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Both a and b explicitly 0, so result = 0 | 0 = 0.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 11. Multiple always_comb blocks all evaluate at time 0.
// ---------------------------------------------------------------------------
TEST(SimCh9b, MultipleAlwaysCombTime0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  always_comb x = 8'h11;\n"
      "  always_comb y = 8'h22;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0x11u}, {"y", 0x22u}});
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

}  // namespace
