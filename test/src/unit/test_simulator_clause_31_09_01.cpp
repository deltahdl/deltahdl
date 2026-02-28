// §31.9.1: Requirements for accurate simulation

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.2 Sim — delayed_data with bracket index simulates
// =============================================================================
TEST(SimA70502, DelayedDataBracketSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dD[3]);\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

}  // namespace
