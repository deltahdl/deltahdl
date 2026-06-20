#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

// Clause 30.4.3 states two simulator-stage rules for edge-sensitive module
// paths: when a vector port is the source, the edge transition is detected on
// the LSB; and when no edge identifier is given, the path is active on any
// transition. Neither has a production carrier yet -- module path delays are
// not lowered into the scheduler (the lowerer holds no specify references, and
// simulator/specify.cpp handles only system timing checks). This single smoke
// test therefore confirms that an edge-sensitive specify path does not disturb
// the rest of simulation; it does not observe LSB edge detection or the
// any-transition default, since no production code applies them.
namespace {

TEST(SpecifyPathSim, EdgeSensitivePathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
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
