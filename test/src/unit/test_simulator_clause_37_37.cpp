#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.37 "Intermodule path": the VPI object model gives an inter mod path a
// delay property (reached through vpi_get_delays()/vpi_put_delays()), a
// traversal to its ports, and a way in through vpi_handle_multi(). Every
// underlying routine is supplied by the dependencies (§37.14 ports, §38.10
// vpi_get_delays, §38.32 vpi_put_delays, and the generic vpi_handle_multi);
// these tests observe each diagram relation being applied to an object of type
// vpiInterModPath.
class IntermodulePathModel : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // A bare object of the requested kind. CreateModule allocates a context-owned
  // VpiObject; the test then stamps the category it actually wants, the same
  // way the §38.10/§38.32 delay tests build their handles.
  VpiHandle MakeObject(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("imp", "imp");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §37.37 Detail 1: vpi_handle_multi(vpiInterModPath, port1, port2) reaches the
// intermodule path that runs between the two named ports. With the path linked
// from both ports, the multi-handle traversal recovers it.
TEST_F(IntermodulePathModel, ReachedByHandleMultiFromTwoPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port1 = vpi_ctx_.CreatePort("p1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("p2", kVpiOutput, mod);

  VpiHandle path = MakeObject(vpiInterModPath);
  port1->children.push_back(path);
  port2->children.push_back(path);

  vpiHandle reached = VpiHandleMultiC(vpiInterModPath, port1, port2);
  ASSERT_NE(reached, nullptr);
  ASSERT_FALSE(reached->children.empty());
  EXPECT_EQ(reached->children[0]->type, vpiInterModPath);
}

// §37.37 Detail 1 (negative): when the two ports have no intermodule path
// between them, the multi-handle traversal yields nothing to reach.
TEST_F(IntermodulePathModel, NoPathBetweenUnconnectedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top2", "top2");
  auto* port1 = vpi_ctx_.CreatePort("q1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("q2", kVpiOutput, mod);

  EXPECT_EQ(VpiHandleMultiC(vpiInterModPath, port1, port2), nullptr);
}

// §37.37 (delay property): the inter mod path object carries delays that the
// diagram exposes through both vpi_put_delays() and vpi_get_delays(). An
// intermodule path takes two or three delays; written values read back in
// order.
TEST_F(IntermodulePathModel, DelayPropertyRoundTrips) {
  VpiHandle path = MakeObject(vpiInterModPath);
  path->delays = {VpiDelayInfo{}, VpiDelayInfo{}};

  s_vpi_time in[2] = {};
  in[0].real = 5.0;
  in[1].real = 9.0;
  s_vpi_delay put = {};
  put.da = in;
  put.no_of_delays = 2;
  put.time_type = vpiScaledRealTime;
  vpi_put_delays(path, &put);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 5.0);
  EXPECT_DOUBLE_EQ(out[1].real, 9.0);
}

// §37.37 (ports relation): the diagram's arrow from an inter mod path to ports
// is a one-to-many traversal. Iterating ports from the path walks the ports it
// connects.
TEST_F(IntermodulePathModel, TraversesToItsPorts) {
  auto* mod = vpi_ctx_.CreateModule("top3", "top3");
  auto* port1 = vpi_ctx_.CreatePort("r1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("r2", kVpiOutput, mod);

  VpiHandle path = MakeObject(vpiInterModPath);
  path->children.push_back(port1);
  path->children.push_back(port2);

  vpiHandle iter = vpi_iterate(vpiPort, path);
  ASSERT_NE(iter, nullptr);

  std::vector<vpiHandle> seen;
  while (vpiHandle p = vpi_scan(iter)) seen.push_back(p);
  EXPECT_EQ(static_cast<int>(seen.size()), 2);
  EXPECT_EQ(seen[0], port1);
  EXPECT_EQ(seen[1], port2);
}

}  // namespace
}  // namespace delta
