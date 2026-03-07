#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.5: Variable initialization occurs before initial blocks.
TEST(SimCh10c, VarInitBeforeInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 42;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // y should see x's initialized value of 42.
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

// §10.5: Variable initialization is not a continuous assignment.
TEST(SimCh10c, VarInitIsNotContinuous) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    a = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  // a is overwritten by the blocking assign.
  EXPECT_EQ(a->value.ToUint64(), 99u);
  // b captured a's initialized value (10), not the later value.
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

// §10.5: Variable holds initialized value until next assignment.
TEST(SimCh10c, VarInitHoldsUntilAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  // No assignments occurred, so x retains its initialized value.
  EXPECT_EQ(x->value.ToUint64(), 100u);
}

// §10.5: Logic variable with expression initializer.
TEST(SimCh10c, VarInitWithExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v = 8'hF0 & 8'h3C;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x30u);
}

// §10.5: Multiple variables initialized in one declaration.
TEST(SimCh10c, MultipleVarInitSameDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}

// §10.5: Variable initialization before always block.
TEST(SimCh10c, VarInitBeforeAlwaysBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] count = 8'd5;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    result <= count;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  // always_ff fires on posedge clk, capturing count's initialized value.
  EXPECT_EQ(result->value.ToUint64(), 5u);
}

}  // namespace
