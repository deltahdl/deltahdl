#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.5: a specify block using the bare `edge` keyword lowers and
// simulates without disturbing unrelated initial assignments.
TEST(EdgeControlSpecifierSim, EdgeKeywordSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, edge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
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

// §31.5 Syntax 31-15: a descriptor list `[01, 10]` survives lowering and
// simulation alongside an unrelated initial block.
TEST(EdgeControlSpecifierSim, Descriptors01And10Simulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, edge [01, 10] clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §31.5: "Edge transitions involving z are treated the same way as edge
// transitions involving x" — a z-form descriptor list lowers and simulates
// without surfacing a lowering error distinct from the x form.
TEST(EdgeControlSpecifierSim, ZTransitionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $hold(edge [z0, z1] clk, data, 5);\n"
      "  endspecify\n"
      "  initial x = 8'd44;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §31.5 Syntax 31-15: the `z_or_x zero_or_one` form (e.g. `x0`, `x1`)
// lowers and simulates alongside an unrelated initial block. The §31.5
// x/z equivalence statement makes the x case warrant the same end-to-end
// coverage the z case already has.
TEST(EdgeControlSpecifierSim, XTransitionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, edge [x0, x1] clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
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

// §31.5 Syntax 31-15: the `zero_or_one z_or_x` form is the third
// edge_descriptor alternative and must survive the full pipeline like
// the other two.
TEST(EdgeControlSpecifierSim, ToXTransitionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, edge [0x, 1x] clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
