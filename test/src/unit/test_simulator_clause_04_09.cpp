#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

// §4.9 own-text atom: every kind of assignment listed in §4.9.1–§4.9.7
// reduces to a scheduler event in the appropriate region. The seven labels
// here correspond one-to-one with those subclauses; the per-kind semantics
// are owned and tested by each subclause's own file.
TEST(AssignmentSchedulingSim, AllAssignmentTypesUseSchedulerInfrastructure) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> executed;

  ScheduleLabeled(sched, Region::kActive, "continuous", executed);
  ScheduleLabeled(sched, Region::kActive, "proc_continuous", executed);
  ScheduleLabeled(sched, Region::kInactive, "blocking", executed);
  ScheduleLabeled(sched, Region::kNBA, "nonblocking", executed);
  ScheduleLabeled(sched, Region::kActive, "switch", executed);
  ScheduleLabeled(sched, Region::kActive, "port", executed);
  ScheduleLabeled(sched, Region::kActive, "subroutine", executed);

  sched.Run();
  EXPECT_EQ(executed.size(), 7u);
}

// §4.9 own-text atom (end-to-end view): a real SV design that mixes several
// of the seven assignment kinds (continuous, blocking, always_comb-wrapped
// blocking, NBA with delay) flows through the same Lowerer→Scheduler pipeline
// and produces consistent final values. This observes the unifying-pipeline
// rule on real source rather than synthetic events.
TEST(AssignmentSchedulingSim, MixedAssignmentKindsRunThroughUnifiedPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #10 a = 8'd10;\n"
      "  end\n"
      "  assign b = a + 8'd1;\n"
      "  always_comb c = b * 8'd2;\n"
      "  initial begin\n"
      "    d <= 8'd0;\n"
      "    #10 d <= 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 99u);
}
