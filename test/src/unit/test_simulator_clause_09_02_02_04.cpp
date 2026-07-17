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

// End-to-end for the §9.2.2.4 canonical example's single event control: an
// always_ff whose one-and-only event control carries a §9.4.2 `iff` guard.
// The flip-flop must capture only on a posedge for which the guard holds, so a
// posedge that arrives while the guard is false leaves the register unchanged.
// Built from real source and run through the full pipeline; observing the held
// value proves the guarded edge -- not an ungated one -- drove the capture.
TEST(AlwaysFFSimulation, IffGuardedEdgeGatesCapture) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    en  = 1;\n"
      "    d   = 8'h11;\n"
      "    q   = 8'h00;\n"
      "    #1 clk = 1;\n"  // posedge with guard true: capture 0x11
      "    #1 clk = 0;\n"
      "       en  = 0;\n"
      "       d   = 8'h22;\n"
      "    #1 clk = 1;\n"  // posedge with guard false: no capture
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0x11u);
}

}  // namespace
