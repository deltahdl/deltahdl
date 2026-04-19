#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST_F(SpecifyTest, RuntimeMultiplePathDelays) {
  SpecifyManager mgr;
  PathDelay pd1;
  pd1.src_port = "in1";
  pd1.dst_port = "out1";
  pd1.delays[0] = 5;
  mgr.AddPathDelay(pd1);

  PathDelay pd2;
  pd2.src_port = "in2";
  pd2.dst_port = "out2";
  pd2.delays[0] = 8;
  pd2.path_kind = SpecifyPathKind::kFull;
  mgr.AddPathDelay(pd2);

  EXPECT_EQ(mgr.PathDelayCount(), 2u);
  EXPECT_EQ(mgr.GetPathDelay("in1", "out1"), 5u);
  EXPECT_EQ(mgr.GetPathDelay("in2", "out2"), 8u);
}

}  // namespace
