#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.37 "Intermodule path": the VPI object model gives an inter mod path a
// delay property (reached through vpi_get_delays()/vpi_put_delays()), a
// traversal to its ports, and a way in through vpi_handle_multi(). Every
// underlying routine is supplied by the dependencies (§37.14 ports, §38.10
// vpi_get_delays, §38.32 vpi_put_delays, and §38.22 vpi_handle_multi);
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

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, port1, port2), path);
}

// §37.37 Detail 1 (negative): when the two ports have no intermodule path
// between them, the multi-handle traversal yields nothing to reach.
TEST_F(IntermodulePathModel, NoPathBetweenUnconnectedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top2", "top2");
  auto* port1 = vpi_ctx_.CreatePort("q1", kVpiInput, mod);
  auto* port2 = vpi_ctx_.CreatePort("q2", kVpiOutput, mod);

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, port1, port2), nullptr);
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

// -----------------------------------------------------------------------------
// Every case above builds the intermodule path it then asks about. Nothing
// under src/ made one, so a run held no path at all: this model answered for
// paths a test had built and for none a design connected.
// -----------------------------------------------------------------------------

// What the application found walking the paths of one design.
int g_path_reached = -1;
int g_unrelated_reached = -1;
int g_path_ports_seen = 0;
std::string g_path_port_names;
double g_path_rise = -1.0;
double g_path_fall = -1.0;

// The port named `port` of the instance named `inst`, reached the way a PLI
// application reaches one: the instance by name, then the ports it declares.
// The scan runs to exhaustion, which is what releases the iterator (§37.2.1).
vpiHandle PortOfInstance(const char* inst, const char* port) {
  vpiHandle mod = vpi_handle_by_name(inst, nullptr);
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

// §37.37 detail 1: the path between two ports, through the multi-handle the
// detail names. §38.22 has that handle name the path itself, so it is what an
// application goes on to use.
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

int WalkPathsCalltf(const char*) {
  vpiHandle a_o = PortOfInstance("a", "o");
  vpiHandle b_i = PortOfInstance("b", "i");
  vpiHandle d_i = PortOfInstance("d", "i");
  if (a_o == nullptr || b_i == nullptr || d_i == nullptr) return 0;

  // a.o and d.i are each on a path, but on no path with each other.
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
  data.tfname = "$probe";
  data.calltf = &WalkPathsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// Two independent connections between one driving instance and one receiving
// instance, so that a port of each pair has a path and the two pairs have none
// between them.
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

// §37.37 detail 1: "To get to an intermodule path, vpi_handle_multi(
// vpiInterModPath, port1, port2) can be used." The two ports one signal runs
// between have a path; two ports on different signals have none.
TEST_F(IntermodulePathInARun, ConnectedPortsReachThePathBetweenThem) {
  RegisterPathProbe();

  SimFixture f;
  RunTwoConnectedPairs(f);

  EXPECT_EQ(g_path_reached, 1);
  EXPECT_EQ(g_unrelated_reached, 0);
}

// §37.37 (the diagram's relation to ports): the path reaches the ports it runs
// between, which are the driving port and the receiving port in that order.
TEST_F(IntermodulePathInARun, ThePathReachesThePortsItRunsBetween) {
  RegisterPathProbe();

  SimFixture f;
  RunTwoConnectedPairs(f);

  ASSERT_EQ(g_path_reached, 1);
  EXPECT_EQ(g_path_ports_seen, 2);
  EXPECT_EQ(g_path_port_names, "oi");
}

// §37.37 (the delay property): the path a design connected takes delays through
// vpi_put_delays() and reports them through vpi_get_delays(), the two routines
// the diagram gives the property.
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
