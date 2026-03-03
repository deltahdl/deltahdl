// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.4.2.4: iff in always block with nonblocking assignment.
TEST(SimCh9e, IffAlwaysBlockNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en)\n"
      "    q <= 123;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

}  // namespace
