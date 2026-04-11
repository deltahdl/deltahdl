#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysFFSimulation, TriggersOnPosedgeClock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, d, q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    d = 1;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

TEST(AlwaysFFSimulation, AsyncResetPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, rst, d;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    rst = 1;\n"
      "    d = 1;\n"
      "    #1 rst = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) q <= 8'h00;\n"
      "    else q <= {7'b0, d};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

TEST(AlwaysFFSimulation, NonblockingAssignSemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    a <= b;\n"
      "    b <= a;\n"
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
  EXPECT_EQ(a->value.ToUint64(), 0x22u);
  EXPECT_EQ(b->value.ToUint64(), 0x11u);
}

}  // namespace
