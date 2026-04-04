#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConcatenationSim, ConcatWithVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hC;\n"
      "    b = 4'h3;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC3u);
}

TEST(ConcatenationSim, ConcatDoesNotInterfere) {
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

TEST(ConcatenationElaboration, ConcatenationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  assign a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, ConstantConcatenationInParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [15:0] P = {8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, ConcatInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  initial a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationSim, ConcatInAlwaysComb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'hB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = {hi, lo};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ConcatenationSim, ConcatRhsTwoVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] c;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0xCAFEu);
}

TEST(ConcatenationSim, LhsConcatUnpacking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 0xCu);
  EXPECT_EQ(vb->value.ToUint64(), 0x3u);
}

TEST(ConcatenationSim, ConcatThreeVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'hB;\n"
      "    c = 4'hC;\n"
      "    result = {a, b, c};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

TEST(ConcatenationSim, NestedConcatSim) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 4'h1;\n"
      "    b = 4'h2;\n"
      "    c = 4'h3;\n"
      "    result = {a, {b, c}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x123u);
}

TEST(ConcatenationSim, ConcatMixedWidths) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 4'hC;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

}  // namespace
