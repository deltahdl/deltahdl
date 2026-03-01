// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// § concatenation — does not interfere with other initial blocks
TEST(SimA81, ConcatDoesNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {4'h1, 4'h2};\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0x12u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}

// § inside_expression — value no match
TEST(SimA83, InsideValueNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd4 inside {8'd3, 8'd5, 8'd7};\n"
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

// § inside_expression — range match
TEST(SimA83, InsideRangeMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd5 inside {[8'd1:8'd10]};\n"
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

// § decimal_number — [size] decimal_base x_digit (all x)
TEST(SimA87, DecimalXDigitAllBits) {
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
  // x fills all bits — check bval is set (four-state x)
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// § octal_value — with underscores
TEST(SimA87, OctalValueUnderscores) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 12'o77_77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 07777u);
}

// § hex_value — with underscores
TEST(SimA87, HexValueUnderscores) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hAB_CD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(VpiAnnexK2, VpiTimeDefaultInit) {
  s_vpi_time time = {};
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(time.high, 0u);
  EXPECT_EQ(time.low, 0u);
  EXPECT_DOUBLE_EQ(time.real, 0.0);
}

// ===========================================================================
// §4.2 Execution of a hardware model and its verification environment
//
// LRM §4.2 establishes the fundamental execution model:
//   - SystemVerilog is a parallel programming language.
//   - Certain constructs execute as parallel blocks or processes.
//   - Understanding guaranteed vs. indeterminate execution order is key.
//   - Semantics are defined for simulation.
//
// These tests verify the simulation-level behaviour of the concepts
// introduced in §4.2, covering parallel process execution, sequential
// ordering within processes, and interaction between concurrent elements.
// ===========================================================================
// ---------------------------------------------------------------------------
// 29. §4.2 Processes are concurrently scheduled elements: always_comb
//     re-evaluates when any input changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, AlwaysCombReEvaluatesOnChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    sel = 8'd0;\n"
      "    #5 sel = 8'd1;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = b;\n"
      "    else\n"
      "      result = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // After #5, sel=1 so result=b=20.
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
