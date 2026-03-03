// §9.4.2: Event control

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, PosedgeWakeup) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 1u);
}

}  // namespace
