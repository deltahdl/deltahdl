#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(MultiBlockExampleSim, TwoBlocksDifferentClocks) {
  ClockingSimFixture f;
  auto* phi1 = f.ctx.CreateVariable("phi1", 1);
  phi1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* phi2 = f.ctx.CreateVariable("phi2", 1);
  phi2->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 16);
  data->value = MakeLogic4VecVal(f.arena, 16, 0x1234);
  auto* cmd = f.ctx.CreateVariable("cmd", 8);
  cmd->value = MakeLogic4VecVal(f.arena, 8, 0x56);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cd1";
  block1.clock_signal = "phi1";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal s1;
  s1.signal_name = "data";
  s1.direction = ClockingDir::kInput;
  block1.signals.push_back(s1);
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cd2";
  block2.clock_signal = "phi2";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{2};
  block2.default_output_skew = SimTime{4};
  ClockingSignal s2;
  s2.signal_name = "cmd";
  s2.direction = ClockingDir::kInout;
  block2.signals.push_back(s2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  // Trigger phi1 posedge — only cd1 samples.
  SchedulePosedge(f, phi1, 10);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cd1", "data"), 0x1234u);
  EXPECT_EQ(cmgr.GetSampledValue("cd2", "cmd"), 0u);  // Not yet triggered.

  // Trigger phi2 posedge — cd2 samples.
  SchedulePosedge(f, phi2, 20);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cd2", "cmd"), 0x56u);
}

}  // namespace
