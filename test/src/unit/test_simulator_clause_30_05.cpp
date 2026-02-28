// §30.5: Assigning delays to module paths

#include "fixture_specify.h"
#include "simulator/specify.h"

namespace {

// =============================================================================
// Runtime SpecifyManager tests
// =============================================================================
TEST_F(SpecifyTest, RuntimePathDelay) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delays[0] = 10;
  pd.delays[1] = 12;
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("a", "b"));
  EXPECT_FALSE(mgr.HasPathDelay("b", "a"));
  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 10u);
  EXPECT_EQ(mgr.GetPathDelay("x", "y"), 0u);
  EXPECT_EQ(mgr.PathDelayCount(), 1u);
}

}  // namespace
