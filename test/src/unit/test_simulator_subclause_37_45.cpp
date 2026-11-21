#include <gtest/gtest.h>

#include <algorithm>
#include <fstream>
#include <ios>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class DelayTerminals : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(DelayTerminals, InAndOutTermsAreReached) {
  VpiObject in_term;
  in_term.type = vpiDelayTerm;
  VpiObject out_term;
  out_term.type = vpiDelayTerm;

  VpiObject device;
  device.type = vpiDelayDevice;
  device.in_term = &in_term;
  device.out_term = &out_term;

  VpiHandle reached_in =
      VpiObjectOf(vpi_handle(vpiInTerm, VpiHandleOf(&device)));
  VpiHandle reached_out =
      VpiObjectOf(vpi_handle(vpiOutTerm, VpiHandleOf(&device)));
  EXPECT_EQ(reached_in, &in_term);
  EXPECT_EQ(reached_out, &out_term);

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_in)), vpiDelayTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_out)), vpiDelayTerm);
}

TEST_F(DelayTerminals, TermRelationsAreNullWhenAbsent) {
  VpiObject device;
  device.type = vpiDelayDevice;

  EXPECT_EQ(vpi_handle(vpiInTerm, VpiHandleOf(&device)), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, VpiHandleOf(&device)), nullptr);
}

TEST_F(DelayTerminals, TermRelationsApplyOnlyToDelayDevices) {
  VpiObject stray_term;
  stray_term.type = vpiDelayTerm;

  VpiObject not_a_device;
  not_a_device.type = vpiModule;
  not_a_device.children = {&stray_term};
  not_a_device.in_term = &stray_term;
  not_a_device.out_term = &stray_term;

  EXPECT_EQ(vpi_handle(vpiInTerm, VpiHandleOf(&not_a_device)), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, VpiHandleOf(&not_a_device)), nullptr);
}

TEST_F(DelayTerminals, DelayTypeIsReported) {
  VpiObject device;
  device.type = vpiDelayDevice;
  device.delay_type = 3;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&device)), 3);

  VpiObject term;
  term.type = vpiDelayTerm;
  term.delay_type = 5;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&term)), 5);

  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&other)), 0);
}

TEST_F(DelayTerminals, ModuleRelationReachesEnclosingModule) {
  VpiObject module_scope;
  module_scope.type = vpiModule;

  VpiObject device;
  device.type = vpiDelayDevice;
  device.parent = &module_scope;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, VpiHandleOf(&device))),
            &module_scope);

  VpiObject orphan;
  orphan.type = vpiDelayDevice;
  EXPECT_EQ(vpi_handle(vpiModule, VpiHandleOf(&orphan)), nullptr);
}

TEST_F(DelayTerminals, DriverFromATerminalReachesTheNetDriverKinds) {
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;
  prim_term.direction = vpiOutput;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;

  VpiObject in_term;
  in_term.type = vpiDelayTerm;
  in_term.children = {&prim_term, &assign_stmt};

  vpiHandle itr = vpi_iterate(vpiDriver, VpiHandleOf(&in_term));
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &prim_term);
  EXPECT_EQ(vpi_scan(itr), nullptr);
}

TEST_F(DelayTerminals, LoadFromATerminalReachesTheNetLoadKinds) {
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject port;
  port.type = vpiPort;

  VpiObject out_term;
  out_term.type = vpiDelayTerm;
  out_term.children = {&assign_stmt, &port};

  vpiHandle itr = vpi_iterate(vpiLoad, VpiHandleOf(&out_term));
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &assign_stmt);
  EXPECT_EQ(vpi_scan(itr), nullptr);
}

TEST_F(DelayTerminals, AnInputTermOnANetWithNoRunNetReadsTheNet) {
  Arena arena;
  Variable storage;
  storage.value = MakeLogic4VecVal(arena, 1, 1);
  VpiObject net;
  net.type = vpiNet;
  net.var = &storage;
  VpiObject device;
  device.type = vpiDelayDevice;
  VpiObject in_term;
  in_term.type = vpiDelayTerm;
  in_term.parent = &device;
  in_term.term_net = &net;
  device.in_term = &in_term;

  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(VpiHandleOf(&in_term), &value);
  EXPECT_EQ(value.value.integer, 1);
}

vpiHandle DeviceOfKindOnNet(const char* name, int kind) {
  vpiHandle net = vpi_handle_by_name(VpiText(name), nullptr);
  vpiHandle it = net == nullptr ? nullptr : vpi_iterate(vpiLoad, net);
  if (it == nullptr) return nullptr;
  while (vpiHandle load = vpi_scan(it)) {
    if (vpi_get(vpiType, load) != vpiDelayTerm) continue;
    vpiHandle device = vpi_handle(vpiDelayDevice, load);
    if (vpi_get(vpiDelayType, device) == kind) return device;
  }
  return nullptr;
}

int TermScalar(vpiHandle device, int relation) {
  s_vpi_value value = {};
  value.format = vpiScalarVal;
  vpi_get_value(vpi_handle(relation, device), &value);
  return value.value.scalar;
}

int g_in_term_mid_delay = -1;
int g_out_term_mid_delay = -1;
const char* g_peeked_net = nullptr;
int g_peeked_kind = vpiModPathDelay;

PLI_INT32 PeekDelayTermsCalltf(PLI_BYTE8*) {
  vpiHandle device = DeviceOfKindOnNet(g_peeked_net, g_peeked_kind);
  if (device == nullptr) return 0;
  g_in_term_mid_delay = TermScalar(device, vpiInTerm);
  g_out_term_mid_delay = TermScalar(device, vpiOutTerm);
  return 0;
}

void RegisterPeek(const char* net, int kind = vpiModPathDelay) {
  g_in_term_mid_delay = -1;
  g_out_term_mid_delay = -1;
  g_peeked_net = net;
  g_peeked_kind = kind;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$peek");
  data.calltf = &PeekDelayTermsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void PutRiseAndFall(vpiHandle obj, PLI_UINT32 rise, PLI_UINT32 fall) {
  s_vpi_time times[2] = {};
  times[0].type = vpiSimTime;
  times[0].low = rise;
  times[1].type = vpiSimTime;
  times[1].low = fall;
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(obj, &delay);
}

vpiHandle PortNamed(const char* module, const char* name) {
  vpiHandle it =
      vpi_iterate(vpiPort, vpi_handle_by_name(VpiText(module), nullptr));
  if (it == nullptr) return nullptr;
  while (vpiHandle port = vpi_scan(it)) {
    if (std::string(vpi_get_str(vpiName, port)) == name) return port;
  }
  return nullptr;
}

vpiHandle IntermodulePathOfTop() {
  return vpi_handle_multi(vpiInterModPath, PortNamed("top.d", "o"),
                          PortNamed("top.r", "i"));
}

int g_put_kind = vpiInterModPathDelay;

PLI_INT32 PutADelayCalltf(PLI_BYTE8*) {
  vpiHandle target = g_put_kind == vpiInterModPathDelay
                         ? IntermodulePathOfTop()
                         : PortNamed("top.r", "i");
  if (target != nullptr) PutRiseAndFall(target, 3, 3);
  return 0;
}

void RegisterPut(int kind) {
  g_put_kind = kind;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$putdelay");
  data.calltf = &PutADelayCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

std::string WriteSdf(const std::string& name, const std::string& entries) {
  const std::string kPath = "/tmp/delta_c37_45_" + name + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY "
         "(ABSOLUTE "
      << entries << "))))";
  return kPath;
}

class DelayDevicesOfARun : public VpiDesignRun {
 protected:
  void RunACellWithAPath() {
    Run("module m(input a, output y);\n"
        "  buf g(y, a);\n"
        "  specify (a => y) = 3; endspecify\n"
        "endmodule\n"
        "module top; wire p, q; m u(p, q); endmodule\n");
  }

  static std::vector<vpiHandle> TermsOf(int type, vpiHandle ref) {
    std::vector<vpiHandle> terms = ObjectsOf(type, ref);
    std::erase_if(
        terms, [](vpiHandle h) { return vpi_get(vpiType, h) != vpiDelayTerm; });
    return terms;
  }

  static bool HoldsObject(const std::vector<vpiHandle>& objects, vpiHandle h) {
    return std::ranges::any_of(
        objects, [h](vpiHandle o) { return VpiObjectOf(o) == VpiObjectOf(h); });
  }
};

TEST_F(DelayDevicesOfARun, AModulePathPlacesADeviceOnItsOutputNet) {
  RunACellWithAPath();
  vpiHandle y = By("top.u.y");
  ASSERT_NE(y, nullptr);
  const std::vector<vpiHandle> kLoadTerms = TermsOf(vpiLoad, y);
  ASSERT_EQ(kLoadTerms.size(), 1u);
  vpiHandle device = vpi_handle(vpiDelayDevice, kLoadTerms[0]);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(vpi_get(vpiType, device), vpiDelayDevice);
  EXPECT_EQ(vpi_get(vpiDelayType, device), vpiModPathDelay);
  EXPECT_EQ(vpi_get(vpiDelayType, kLoadTerms[0]), vpiModPathDelay);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInTerm, device)),
            VpiObjectOf(kLoadTerms[0]));
  vpiHandle module = vpi_handle(vpiModule, device);
  ASSERT_NE(module, nullptr);
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, module)), "top.u");

  const std::vector<vpiHandle> kDriverTerms = TermsOf(vpiDriver, y);
  ASSERT_EQ(kDriverTerms.size(), 1u);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiOutTerm, device)),
            VpiObjectOf(kDriverTerms[0]));
}

TEST_F(DelayDevicesOfARun, ATermReachesTheNetsDriversOrLoadsLessItsDevice) {
  RunACellWithAPath();
  vpiHandle y = By("top.u.y");
  ASSERT_NE(y, nullptr);
  const std::vector<vpiHandle> kLoadTerms = TermsOf(vpiLoad, y);
  ASSERT_EQ(kLoadTerms.size(), 1u);
  vpiHandle device = vpi_handle(vpiDelayDevice, kLoadTerms[0]);
  ASSERT_NE(device, nullptr);
  vpiHandle in_term = vpi_handle(vpiInTerm, device);
  vpiHandle out_term = vpi_handle(vpiOutTerm, device);

  const std::vector<int> kInDrivers = KindsOf(vpiDriver, in_term);
  EXPECT_NE(std::ranges::find(kInDrivers, vpiPrimTerm), kInDrivers.end());
  EXPECT_FALSE(HoldsObject(ObjectsOf(vpiDriver, in_term), out_term));
  EXPECT_FALSE(HoldsObject(ObjectsOf(vpiLoad, out_term), in_term));
}

TEST_F(DelayDevicesOfARun, AModuleIteratesNoDelayDevice) {
  RunACellWithAPath();
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_iterate(vpiDelayDevice, u), nullptr);
}

TEST_F(DelayDevicesOfARun, NoPathPlacesNoDevice) {
  Run("module m(input a, output y); buf g(y, a); endmodule\n"
      "module top; wire p, q; m u(p, q); endmodule\n");
  vpiHandle y = By("top.u.y");
  ASSERT_NE(y, nullptr);
  EXPECT_TRUE(TermsOf(vpiLoad, y).empty());
  EXPECT_TRUE(TermsOf(vpiDriver, y).empty());
}

TEST_F(DelayDevicesOfARun, APathIntoAVariablePlacesNoDevice) {
  Run("module m(input a, output reg y);\n"
      "  always @(a) y = a;\n"
      "  specify (a => y) = 3; endspecify\n"
      "endmodule\n"
      "module top; wire p, q; m u(p, q); endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_NE(vpi_iterate(vpiModPath, u), nullptr);
  vpiHandle q = By("top.q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(TermsOf(vpiLoad, q).empty());
  EXPECT_TRUE(TermsOf(vpiDriver, q).empty());
}

TEST_F(DelayDevicesOfARun, APutOnAnIntermodulePathPlacesADevice) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module top; wire w; drv d(w); rcv r(w); endmodule\n");
  vpiHandle from = Named(vpiPort, By("top.d"), "o");
  vpiHandle to = Named(vpiPort, By("top.r"), "i");
  ASSERT_NE(from, nullptr);
  ASSERT_NE(to, nullptr);
  vpiHandle path = vpi_handle_multi(vpiInterModPath, from, to);
  ASSERT_NE(path, nullptr);
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(TermsOf(vpiLoad, w).empty());

  PutRiseAndFall(path, 4, 6);
  PutRiseAndFall(path, 4, 6);

  const std::vector<vpiHandle> kLoadTerms = TermsOf(vpiLoad, w);
  ASSERT_EQ(kLoadTerms.size(), 1u);
  vpiHandle device = vpi_handle(vpiDelayDevice, kLoadTerms[0]);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(vpi_get(vpiDelayType, device), vpiInterModPathDelay);
  vpiHandle module = vpi_handle(vpiModule, device);
  ASSERT_NE(module, nullptr);
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, module)), "top");
  EXPECT_EQ(TermsOf(vpiDriver, w).size(), 1u);
}

TEST_F(DelayDevicesOfARun, APutOnAnInputPortPlacesADevice) {
  Run("module rcv(input i); endmodule\n"
      "module top; wire w; rcv r(w); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.r"), "i");
  ASSERT_NE(port, nullptr);
  vpiHandle i = By("top.r.i");
  ASSERT_NE(i, nullptr);
  EXPECT_TRUE(TermsOf(vpiLoad, i).empty());

  PutRiseAndFall(port, 4, 6);
  PutRiseAndFall(port, 4, 6);

  const std::vector<vpiHandle> kLoadTerms = TermsOf(vpiLoad, i);
  ASSERT_EQ(kLoadTerms.size(), 1u);
  vpiHandle device = vpi_handle(vpiDelayDevice, kLoadTerms[0]);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(vpi_get(vpiDelayType, device), vpiMIPDelay);
  vpiHandle module = vpi_handle(vpiModule, device);
  ASSERT_NE(module, nullptr);
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, module)), "top.r");
  EXPECT_EQ(TermsOf(vpiDriver, i).size(), 1u);
  EXPECT_TRUE(TermsOf(vpiLocalLoad, By("top.w")).empty());
}

TEST_F(DelayDevicesOfARun, APutOnAPortIntoAVariablePlacesNoDevice) {
  Run("module rcv(input var logic i); endmodule\n"
      "module top; logic w; rcv r(w); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.r"), "i");
  ASSERT_NE(port, nullptr);
  s_vpi_time times[2] = {};
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(port, &delay);
  EXPECT_EQ(DeviceOfKindOnNet("top.r.i", vpiMIPDelay), nullptr);
  EXPECT_EQ(DeviceOfKindOnNet("top.w", vpiMIPDelay), nullptr);
}

TEST_F(DelayDevicesOfARun, TheInputTermChangesBeforeTheDelayAndTheOutputAfter) {
  RegisterPeek("top.u.y");
  Run("module m(input a, output y); timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a;\n"
      "  specify (a => y) = 3; endspecify\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic p = 0; wire q; m u(p, q);\n"
      "  initial begin #10 p = 1; #1 $peek; end\n"
      "endmodule\n");
  EXPECT_EQ(g_in_term_mid_delay, vpi1);
  EXPECT_NE(g_out_term_mid_delay, vpi1);
  vpiHandle device = DeviceOfKindOnNet("top.u.y", vpiModPathDelay);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(TermScalar(device, vpiInTerm), vpi1);
  EXPECT_EQ(TermScalar(device, vpiOutTerm), vpi1);
}

TEST_F(DelayDevicesOfARun, ATopModulesOutputTermReadsItsOwnNet) {
  RegisterPeek("top.y");
  Run("module top(input a, output y); timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a;\n"
      "  specify (a => y) = 3; endspecify\n"
      "  initial begin #10 force a = 1; #1 $peek; end\n"
      "endmodule\n");
  EXPECT_EQ(g_in_term_mid_delay, vpi1);
  EXPECT_NE(g_out_term_mid_delay, vpi1);
  vpiHandle device = DeviceOfKindOnNet("top.y", vpiModPathDelay);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(TermScalar(device, vpiInTerm), vpi1);
  EXPECT_EQ(TermScalar(device, vpiOutTerm), vpi1);
}

std::string WriteInterconnectAndPortSdf() {
  return WriteSdf("devices", "(INTERCONNECT u1/o u2/i (10)) (PORT u2/i (5))");
}

std::string ModuleOf(vpiHandle device) {
  vpiHandle module = vpi_handle(vpiModule, device);
  return module == nullptr ? "" : vpi_get_str(vpiFullName, module);
}

TEST_F(DelayDevicesOfARun, AnAnnotatedInterconnectAndPortPlaceDevices) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module top; wire w; drv u1(w); rcv u2(w);\n"
      "  initial #1 $sdf_annotate(\"" +
      WriteInterconnectAndPortSdf() +
      "\");\n"
      "endmodule\n");
  vpiHandle path_device = DeviceOfKindOnNet("top.w", vpiInterModPathDelay);
  ASSERT_NE(path_device, nullptr);
  EXPECT_EQ(ModuleOf(path_device), "top");
  vpiHandle port_device = DeviceOfKindOnNet("top.u2.i", vpiMIPDelay);
  ASSERT_NE(port_device, nullptr);
  EXPECT_EQ(ModuleOf(port_device), "top.u2");
}

TEST_F(DelayDevicesOfARun, AnUnannotatedDesignHoldsNoSdfDevice) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module top; wire w; drv u1(w); rcv u2(w); endmodule\n");
  EXPECT_EQ(DeviceOfKindOnNet("top.w", vpiInterModPathDelay), nullptr);
  EXPECT_EQ(DeviceOfKindOnNet("top.u2.i", vpiMIPDelay), nullptr);
}

struct DeviceSource {
  const char* name;
  int kind;
  const char* net;
  bool annotated;
};

std::string DeviceDesign(const DeviceSource& source) {
  const std::string kStart =
      source.annotated
          ? std::string("$sdf_annotate(\"") +
                WriteSdf(source.name, source.kind == vpiInterModPathDelay
                                          ? "(INTERCONNECT d/o r/i (3))"
                                          : "(PORT r/i (3))") +
                "\");"
          : std::string("$putdelay;");
  return "module drv(input a, output o); assign o = a; endmodule\n"
         "module rcv(input i); endmodule\n"
         "module top;\n"
         "  logic p = 0; wire w; drv d(p, w); rcv r(w);\n"
         "  initial begin " +
         kStart +
         " #10 p = 1; #1 $peek; end\n"
         "endmodule\n";
}

class EveryDeviceKind : public DelayDevicesOfARun,
                        public ::testing::WithParamInterface<DeviceSource> {
 protected:
  vpiHandle RunAndFindDevice() {
    RegisterPut(GetParam().kind);
    RegisterPeek(GetParam().net, GetParam().kind);
    Run(DeviceDesign(GetParam()));
    return DeviceOfKindOnNet(GetParam().net, GetParam().kind);
  }

  static std::vector<vpiHandle> NetObjectsBesideDevices(int relation,
                                                        vpiHandle net) {
    std::vector<vpiHandle> objects = ObjectsOf(relation, net);
    std::erase_if(objects, [](vpiHandle h) {
      return vpi_get(vpiType, h) == vpiDelayTerm;
    });
    return objects;
  }

  static bool SameObjects(const std::vector<vpiHandle>& a,
                          const std::vector<vpiHandle>& b) {
    return a.size() == b.size() && std::ranges::all_of(a, [&](vpiHandle h) {
             return HoldsObject(b, h);
           });
  }
};

TEST_P(EveryDeviceKind, ADeviceReachesBothTermsOnItsNet) {
  vpiHandle device = RunAndFindDevice();
  ASSERT_NE(device, nullptr);
  vpiHandle net = By(GetParam().net);
  vpiHandle in_term = vpi_handle(vpiInTerm, device);
  vpiHandle out_term = vpi_handle(vpiOutTerm, device);
  ASSERT_NE(in_term, nullptr);
  ASSERT_NE(out_term, nullptr);
  EXPECT_EQ(vpi_get(vpiType, in_term), vpiDelayTerm);
  EXPECT_EQ(vpi_get(vpiType, out_term), vpiDelayTerm);
  EXPECT_TRUE(HoldsObject(TermsOf(vpiLoad, net), in_term));
  EXPECT_TRUE(HoldsObject(TermsOf(vpiDriver, net), out_term));
}

TEST_P(EveryDeviceKind, EachTermReportsItsDevicesKind) {
  vpiHandle device = RunAndFindDevice();
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(vpi_get(vpiDelayType, vpi_handle(vpiInTerm, device)),
            GetParam().kind);
  EXPECT_EQ(vpi_get(vpiDelayType, vpi_handle(vpiOutTerm, device)),
            GetParam().kind);
}

TEST_P(EveryDeviceKind, TheOutputTermReachesItsDevice) {
  vpiHandle device = RunAndFindDevice();
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiDelayDevice, vpi_handle(vpiOutTerm, device))),
      VpiObjectOf(device));
}

TEST_P(EveryDeviceKind, DISABLED_TheTermsIterateTheDriversAndLoadsOfTheirNet) {
  vpiHandle device = RunAndFindDevice();
  ASSERT_NE(device, nullptr);
  vpiHandle net = By(GetParam().net);
  vpiHandle in_term = vpi_handle(vpiInTerm, device);
  vpiHandle out_term = vpi_handle(vpiOutTerm, device);
  const std::vector<vpiHandle> kNetDrivers =
      NetObjectsBesideDevices(vpiDriver, net);
  const std::vector<vpiHandle> kNetLoads =
      NetObjectsBesideDevices(vpiLoad, net);
  EXPECT_FALSE(kNetDrivers.empty());
  EXPECT_TRUE(
      SameObjects(NetObjectsBesideDevices(vpiDriver, in_term), kNetDrivers));
  EXPECT_TRUE(
      SameObjects(NetObjectsBesideDevices(vpiLoad, out_term), kNetLoads));
  EXPECT_FALSE(HoldsObject(ObjectsOf(vpiDriver, in_term), out_term));
  EXPECT_FALSE(HoldsObject(ObjectsOf(vpiLoad, out_term), in_term));
}

void ExpectTheInputTermChangedBeforeTheDelay() {
  EXPECT_EQ(g_in_term_mid_delay, vpi1);
}

void ExpectTheOutputTermHeldUntilAfterTheDelay(vpiHandle device) {
  EXPECT_EQ(g_out_term_mid_delay, vpi0);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(TermScalar(device, vpiInTerm), vpi1);
  EXPECT_EQ(TermScalar(device, vpiOutTerm), vpi1);
}

std::string DeviceSourceName(
    const ::testing::TestParamInfo<DeviceSource>& info) {
  return info.param.name;
}

constexpr DeviceSource kPutIntermodulePath{
    "PutIntermodulePath", vpiInterModPathDelay, "top.w", false};
constexpr DeviceSource kPutInputPort{"PutInputPort", vpiMIPDelay, "top.r.i",
                                     false};
constexpr DeviceSource kAnnotatedInterconnect{
    "AnnotatedInterconnect", vpiInterModPathDelay, "top.w", true};
constexpr DeviceSource kAnnotatedPort{"AnnotatedPort", vpiMIPDelay, "top.r.i",
                                      true};

INSTANTIATE_TEST_SUITE_P(PlacedByAPutOrAnAnnotation, EveryDeviceKind,
                         ::testing::Values(kPutIntermodulePath, kPutInputPort,
                                           kAnnotatedInterconnect,
                                           kAnnotatedPort),
                         DeviceSourceName);

class IntermodulePathDevices : public EveryDeviceKind {};

TEST_P(IntermodulePathDevices, TheInputTermChangesBeforeTheDelay) {
  RunAndFindDevice();
  ExpectTheInputTermChangedBeforeTheDelay();
}

TEST_P(IntermodulePathDevices, DISABLED_TheOutputTermChangesOnlyAfterTheDelay) {
  ExpectTheOutputTermHeldUntilAfterTheDelay(RunAndFindDevice());
}

INSTANTIATE_TEST_SUITE_P(PlacedByAPutOrAnAnnotation, IntermodulePathDevices,
                         ::testing::Values(kPutIntermodulePath,
                                           kAnnotatedInterconnect),
                         DeviceSourceName);

class InputPortDevices : public EveryDeviceKind {};

TEST_P(InputPortDevices, DISABLED_TheInputTermChangesBeforeTheDelay) {
  RunAndFindDevice();
  ExpectTheInputTermChangedBeforeTheDelay();
}

TEST_P(InputPortDevices, TheOutputTermChangesOnlyAfterTheDelay) {
  ExpectTheOutputTermHeldUntilAfterTheDelay(RunAndFindDevice());
}

INSTANTIATE_TEST_SUITE_P(PlacedByAPutOrAnAnnotation, InputPortDevices,
                         ::testing::Values(kPutInputPort, kAnnotatedPort),
                         DeviceSourceName);

TEST_F(DelayDevicesOfARun, AModulePathsOutputTermReachesItsDevice) {
  RunACellWithAPath();
  vpiHandle device = DeviceOfKindOnNet("top.u.y", vpiModPathDelay);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiDelayDevice, vpi_handle(vpiOutTerm, device))),
      VpiObjectOf(device));
}

TEST_F(DelayDevicesOfARun,
       DISABLED_AnObjectWithoutADelayTypeReportsItUndefined) {
  RunACellWithAPath();
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_get(vpiDelayType, u), vpiUndefined);
  vpiHandle device = DeviceOfKindOnNet("top.u.y", vpiModPathDelay);
  ASSERT_NE(device, nullptr);
  EXPECT_EQ(vpi_get(vpiDelayType, device), vpiModPathDelay);
}

}  // namespace
}  // namespace delta
