#include <gtest/gtest.h>

#include <algorithm>
#include <fstream>
#include <ios>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.45 Delay terminals: the object model diagram for a delay device and its
// two delay terminals. A delay device reaches its input delay term through
// vpiInTerm and its output delay term through vpiOutTerm; both terms are delay
// term objects. The delay device and each delay term carry the vpiDelayType
// integer property, and a delay device is enclosed by a module. The subclause's
// two numbered Details fix the run-time ordering of value changes on the
// terminals relative to the device's delay (the input term changes before the
// delay, the output term not until after it); those are event-scheduling
// semantics with no VPI query to observe, so they carry no production hook
// here. The terminal value (vpi_get_value) is the generic value machinery.
// The cross-edges the figure draws from a terminal - vpiDriver to §37.46's
// `net drivers` class and vpiLoad to its `net loads` class - are this clause's
// own, because which class they reach is what the figure says about them; they
// are exercised below. These tests observe the production code that applies the
// delay-device relations, the cross-edges, and the property through the public
// vpi_handle / vpi_iterate / vpi_get dispatch.

// The fixture installs a context so the public entry points run their real
// dispatch over the test objects.
class DelayTerminals : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiInTerm / vpiOutTerm: a delay device reaches its input delay term and its
// output delay term. Both are delay term objects, whose own type differs from
// the relation enum, so the relations resolve to the device's designated terms.
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

  // The handles returned for the terminals have the delay term type.
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_in)), vpiDelayTerm);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(reached_out)), vpiDelayTerm);
}

// vpiInTerm / vpiOutTerm (edge): a delay device that has no designated terminal
// reports a null handle rather than reaching a stray object.
TEST_F(DelayTerminals, TermRelationsAreNullWhenAbsent) {
  VpiObject device;
  device.type = vpiDelayDevice;
  // in_term and out_term left null.

  EXPECT_EQ(vpi_handle(vpiInTerm, VpiHandleOf(&device)), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, VpiHandleOf(&device)), nullptr);
}

// vpiInTerm / vpiOutTerm (scope): the terminal relations are specific to a
// delay device. On an object that is not a delay device, asking for them does
// not reach a stray delay term, even when one is present as a child.
TEST_F(DelayTerminals, TermRelationsApplyOnlyToDelayDevices) {
  VpiObject stray_term;
  stray_term.type = vpiDelayTerm;

  VpiObject not_a_device;
  not_a_device.type = vpiModule;
  not_a_device.children = {&stray_term};
  not_a_device.in_term = &stray_term;   // ignored: object is not a delay device
  not_a_device.out_term = &stray_term;  // ignored: object is not a delay device

  EXPECT_EQ(vpi_handle(vpiInTerm, VpiHandleOf(&not_a_device)), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, VpiHandleOf(&not_a_device)), nullptr);
}

// vpiDelayType: a delay device and a delay term both report their delay-type
// code through vpi_get(vpiDelayType); an object that is neither reports zero.
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

// module -- delay device: a delay device is enclosed by a module, reached
// through the generic parent walk. A delay device with no module parent reports
// none.
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

// The figure's vpiDriver edge, drawn from a delay terminal to the `net drivers`
// class. §37.46 is where that class is drawn, and its members are a port, a
// force, a delay terminal, a continuous assignment or a primitive terminal - a
// different set from §37.21's variable drivers. A delay terminal was named by
// neither reference kind of the net arms, so the relation fell to the variable
// arm and gathered the kinds that drive a variable, which a delay terminal
// connects to none of.
TEST_F(DelayTerminals, DriverFromATerminalReachesTheNetDriverKinds) {
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;  // a net driver, not a variable driver
  prim_term.direction = vpiOutput;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;  // a variable driver, not a net driver

  VpiObject in_term;
  in_term.type = vpiDelayTerm;
  in_term.children = {&prim_term, &assign_stmt};

  vpiHandle itr = vpi_iterate(vpiDriver, VpiHandleOf(&in_term));
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &prim_term);
  EXPECT_EQ(vpi_scan(itr), nullptr);
}

// The same for the figure's vpiLoad edge from the output terminal, drawn to the
// `net loads` class.
TEST_F(DelayTerminals, LoadFromATerminalReachesTheNetLoadKinds) {
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;  // a net load
  VpiObject port;
  port.type = vpiPort;  // a net driver; §37.46 detail 1 keeps a bare one off
                        // the load side

  VpiObject out_term;
  out_term.type = vpiDelayTerm;
  out_term.children = {&assign_stmt, &port};

  vpiHandle itr = vpi_iterate(vpiLoad, VpiHandleOf(&out_term));
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(itr)), &assign_stmt);
  EXPECT_EQ(vpi_scan(itr), nullptr);
}

// The delay device of vpiDelayType `kind` whose input term is among the loads
// of the net `name` names, null for none.
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

// The scalar value the delay term `relation` reaches from `device` reads.
int TermScalar(vpiHandle device, int relation) {
  s_vpi_value value = {};
  value.format = vpiScalarVal;
  vpi_get_value(vpi_handle(relation, device), &value);
  return value.value.scalar;
}

// What the two terms of the device on the net a $peek names read while the
// delay is still running.
int g_in_term_mid_delay = -1;
int g_out_term_mid_delay = -1;
const char* g_peeked_net = nullptr;

PLI_INT32 PeekDelayTermsCalltf(PLI_BYTE8* /*user_data*/) {
  vpiHandle device = DeviceOfKindOnNet(g_peeked_net, vpiModPathDelay);
  if (device == nullptr) return 0;
  g_in_term_mid_delay = TermScalar(device, vpiInTerm);
  g_out_term_mid_delay = TermScalar(device, vpiOutTerm);
  return 0;
}

void RegisterPeek(const char* net) {
  g_in_term_mid_delay = -1;
  g_out_term_mid_delay = -1;
  g_peeked_net = net;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$peek");
  data.calltf = &PeekDelayTermsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// The delay devices of a run: the one a module path a specify block declares
// places on the net its output terminal names (#7168), the values its terms
// read (#7363), and those an annotated SDF entry (#7361) and a delay put on an
// intermodule path (#7362) place.
class DelayDevicesOfARun : public VpiDesignRun {
 protected:
  // A cell whose buffer drives y, with a delay of 3 on the path from a to y,
  // instantiated as top.u.
  void RunACellWithAPath() {
    Run("module m(input a, output y);\n"
        "  buf g(y, a);\n"
        "  specify (a => y) = 3; endspecify\n"
        "endmodule\n"
        "module top; wire p, q; m u(p, q); endmodule\n");
  }

  // The delay terms among the objects of `type` that `ref` reaches.
  static std::vector<vpiHandle> TermsOf(int type, vpiHandle ref) {
    std::vector<vpiHandle> terms = ObjectsOf(type, ref);
    std::erase_if(
        terms, [](vpiHandle h) { return vpi_get(vpiType, h) != vpiDelayTerm; });
    return terms;
  }

  // Whether `objects` holds the object `h` stands for.
  static bool HoldsObject(const std::vector<vpiHandle>& objects, vpiHandle h) {
    return std::ranges::any_of(
        objects, [h](vpiHandle o) { return VpiObjectOf(o) == VpiObjectOf(h); });
  }
};

// The input term is among the output net's loads, and it reaches a device of
// vpiDelayType vpiModPathDelay standing in the cell's instance, whose input
// term it is and whose output term is among the same net's drivers.
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

// The input term's drivers are the net's own, the buffer's output terminal
// among them, and the output term's loads leave out the input term: neither
// term reaches the other device term standing beside it.
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

// §37.5 draws no vpiDelayDevice relation from a module, so the cell's
// instance iterates none even though a device stands in it.
TEST_F(DelayDevicesOfARun, AModuleIteratesNoDelayDevice) {
  RunACellWithAPath();
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_iterate(vpiDelayDevice, u), nullptr);
}

// A cell whose specify block declares no path carries no delay, so its output
// net holds no delay term on either side.
TEST_F(DelayDevicesOfARun, NoPathPlacesNoDevice) {
  Run("module m(input a, output y); buf g(y, a); endmodule\n"
      "module top; wire p, q; m u(p, q); endmodule\n");
  vpiHandle y = By("top.u.y");
  ASSERT_NE(y, nullptr);
  EXPECT_TRUE(TermsOf(vpiLoad, y).empty());
  EXPECT_TRUE(TermsOf(vpiDriver, y).empty());
}

// §30.4.1 lets a module path end on a variable, which is no net for a device
// to sit on: the cell still holds its path, and the net its output port drives
// above holds no delay term on either side.
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

// An intermodule path given a delay with vpi_put_delays places a device of
// vpiDelayType vpiInterModPathDelay on the net its two ports share, in the
// module holding that net; before the put the net holds no delay term, and a
// second put leaves the one device standing (#7362).
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

  s_vpi_time times[2] = {};
  times[0].type = vpiSimTime;
  times[0].low = 4;
  times[1].type = vpiSimTime;
  times[1].low = 6;
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(path, &delay);
  vpi_put_delays(path, &delay);

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

// Details 1 and 2 for a path into an instance's output port, whose delay the
// run applies where the port drives the net above: a rise reaching the cell's
// y at 10 is on the input term at 11, while the output term, past the delay
// of 3, has not yet risen; once the run is over both have (#7363).
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

// The same for a path into a top module's own output, whose delay the run
// applies to the net itself: the input term reads the value the transition
// is still carrying across the delay, the output term the net (#7363).
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

// An SDF file whose one cell, the top module, annotates an INTERCONNECT from
// u1's output port o to u2's input port i with a delay of 10, and a PORT delay
// of 5 on u2's i, written where $sdf_annotate opens it (§32.9).
std::string WriteInterconnectAndPortSdf() {
  const std::string kPath = "/tmp/delta_c37_45_devices.sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY "
         "(ABSOLUTE (INTERCONNECT u1/o u2/i (10)) (PORT u2/i (5))))))";
  return kPath;
}

// The full name of the module the delay device `device` reaches.
std::string ModuleOf(vpiHandle device) {
  vpiHandle module = vpi_handle(vpiModule, device);
  return module == nullptr ? "" : vpi_get_str(vpiFullName, module);
}

// An annotated INTERCONNECT places an intermodule path delay device on the net
// its two ports share, in the top module holding it, and an annotated PORT a
// module input port delay device on the net u2's port i connects inside u2
// (#7361).
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

// The same design with no $sdf_annotate call holds no delay on either net, so
// neither holds a device.
TEST_F(DelayDevicesOfARun, AnUnannotatedDesignHoldsNoSdfDevice) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module top; wire w; drv u1(w); rcv u2(w); endmodule\n");
  EXPECT_EQ(DeviceOfKindOnNet("top.w", vpiInterModPathDelay), nullptr);
  EXPECT_EQ(DeviceOfKindOnNet("top.u2.i", vpiMIPDelay), nullptr);
}

}  // namespace
}  // namespace delta
