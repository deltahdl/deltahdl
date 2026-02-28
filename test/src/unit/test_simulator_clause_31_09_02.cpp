// §31.9.2: Conditions in negative timing checks

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.2 Sim — $setuphold with mintypmax timestamp_condition simulates
// =============================================================================
TEST(SimA70502, SetupholdMinTypMaxConditionsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
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

}  // namespace
