// §31.4.6: $nochange


#include "simulation/lowerer.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 Runtime — $nochange stores two offsets
// =============================================================================
TEST(SimA70501, NochangeOffsetsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.limit = 0;   // start_edge_offset
  tc.limit2 = 0;  // end_edge_offset
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kNochange);
}

// =============================================================================
// A.7.5.2 Sim — $nochange with mintypmax offsets simulates
// =============================================================================
TEST(SimA70502, NochangeMinTypMaxOffsetsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

}  // namespace
