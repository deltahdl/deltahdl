#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The if(cond) edge-sensitive form is the second Syntax 30-5 alternative;
// its presence must not disturb surrounding behavioral execution.
TEST(SpecifyPathSim, StateDependentEdgeSensitivePathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

}  // namespace
