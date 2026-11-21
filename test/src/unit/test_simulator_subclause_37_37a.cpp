#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class IntermodulePathModel : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle MakeObject(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("imp", "imp");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

TEST_F(IntermodulePathModel, ReachedByHandleMultiFromTwoPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port1 = vpi_ctx_.CreatePort("p1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("p2", kVpiOutput, mod);

  VpiHandle path = MakeObject(vpiInterModPath);
  port1->children.push_back(path);
  port2->children.push_back(path);

  EXPECT_EQ(VpiObjectOf(vpi_handle_multi(vpiInterModPath, VpiHandleOf(port1),
                                         VpiHandleOf(port2))),
            path);
}

TEST_F(IntermodulePathModel, NoPathBetweenUnconnectedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top2", "top2");
  auto* port1 = vpi_ctx_.CreatePort("q1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("q2", kVpiOutput, mod);

  EXPECT_EQ(
      vpi_handle_multi(vpiInterModPath, VpiHandleOf(port1), VpiHandleOf(port2)),
      nullptr);
}

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
  vpi_put_delays(VpiHandleOf(path), &put);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(path), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 5.0);
  EXPECT_DOUBLE_EQ(out[1].real, 9.0);
}

TEST_F(IntermodulePathModel, TraversesToItsPorts) {
  auto* mod = vpi_ctx_.CreateModule("top3", "top3");
  auto* port1 = vpi_ctx_.CreatePort("r1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("r2", kVpiOutput, mod);

  VpiHandle path = MakeObject(vpiInterModPath);
  path->children.push_back(port1);
  path->children.push_back(port2);

  vpiHandle iter = vpi_iterate(vpiPort, VpiHandleOf(path));
  ASSERT_NE(iter, nullptr);

  std::vector<vpiHandle> seen;
  while (vpiHandle p = vpi_scan(iter)) seen.push_back(p);
  EXPECT_EQ(static_cast<int>(seen.size()), 2);
  EXPECT_EQ(VpiObjectOf(seen[0]), port1);
  EXPECT_EQ(VpiObjectOf(seen[1]), port2);
}

int g_path_reached = -1;
int g_unrelated_reached = -1;
int g_path_ports_seen = 0;
std::string g_path_port_names;
double g_path_rise = -1.0;
double g_path_fall = -1.0;

vpiHandle PortOfInstance(const char* inst, const char* port) {
  vpiHandle mod = vpi_handle_by_name(VpiText(inst), nullptr);
  if (mod == nullptr) return nullptr;
  vpiHandle ports = vpi_iterate(vpiPort, mod);
  if (ports == nullptr) return nullptr;

  vpiHandle found = nullptr;
  for (vpiHandle p = vpi_scan(ports); p != nullptr; p = vpi_scan(ports)) {
    const char* name = vpi_get_str(vpiName, p);
    if (name != nullptr && std::string(name) == port) found = p;
  }
  return found;
}

vpiHandle PathBetween(vpiHandle port1, vpiHandle port2) {
  return vpi_handle_multi(vpiInterModPath, port1, port2);
}

void RecordPathPorts(vpiHandle path) {
  vpiHandle ports = vpi_iterate(vpiPort, path);
  if (ports == nullptr) return;
  for (vpiHandle p = vpi_scan(ports); p != nullptr; p = vpi_scan(ports)) {
    ++g_path_ports_seen;
    const char* name = vpi_get_str(vpiName, p);
    if (name != nullptr) g_path_port_names += name;
  }
}

void RecordPathDelays(vpiHandle path) {
  s_vpi_time in[2] = {};
  in[0].real = 3.0;
  in[1].real = 7.0;
  s_vpi_delay put = {};
  put.da = in;
  put.no_of_delays = 2;
  put.time_type = vpiScaledRealTime;
  vpi_put_delays(path, &put);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &get);
  g_path_rise = out[0].real;
  g_path_fall = out[1].real;
}

PLI_INT32 WalkPathsCalltf(PLI_BYTE8*) {
  vpiHandle a_o = PortOfInstance("a", "o");
  vpiHandle b_i = PortOfInstance("b", "i");
  vpiHandle d_i = PortOfInstance("d", "i");
  if (a_o == nullptr || b_i == nullptr || d_i == nullptr) return 0;

  g_unrelated_reached =
      vpi_handle_multi(vpiInterModPath, a_o, d_i) == nullptr ? 0 : 1;

  vpiHandle path = PathBetween(a_o, b_i);
  g_path_reached = path == nullptr ? 0 : 1;
  if (path == nullptr) return 0;
  RecordPathPorts(path);
  RecordPathDelays(path);
  return 0;
}

void RegisterPathProbe() {
  g_path_reached = -1;
  g_unrelated_reached = -1;
  g_path_ports_seen = 0;
  g_path_port_names.clear();
  g_path_rise = -1.0;
  g_path_fall = -1.0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &WalkPathsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunTwoConnectedPairs(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module drv(output o);\n"
      "endmodule\n"
      "module rcv(input i);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  wire x;\n"
      "  drv a(.o(w));\n"
      "  rcv b(.i(w));\n"
      "  drv c(.o(x));\n"
      "  rcv d(.i(x));\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class IntermodulePathInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(IntermodulePathInARun, ConnectedPortsReachThePathBetweenThem) {
  RegisterPathProbe();

  SimFixture f;
  RunTwoConnectedPairs(f);

  EXPECT_EQ(g_path_reached, 1);
  EXPECT_EQ(g_unrelated_reached, 0);
}

TEST_F(IntermodulePathInARun, ThePathReachesThePortsItRunsBetween) {
  RegisterPathProbe();

  SimFixture f;
  RunTwoConnectedPairs(f);

  ASSERT_EQ(g_path_reached, 1);
  EXPECT_EQ(g_path_ports_seen, 2);
  EXPECT_EQ(g_path_port_names, "oi");
}

TEST_F(IntermodulePathInARun, ThePathTakesAndReportsItsDelays) {
  RegisterPathProbe();

  SimFixture f;
  RunTwoConnectedPairs(f);

  ASSERT_EQ(g_path_reached, 1);
  EXPECT_DOUBLE_EQ(g_path_rise, 3.0);
  EXPECT_DOUBLE_EQ(g_path_fall, 7.0);
}

}  // namespace
}  // namespace delta
