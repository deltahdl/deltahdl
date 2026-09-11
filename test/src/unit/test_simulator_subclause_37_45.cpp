#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

  VpiHandle reached_in = vpi_handle(vpiInTerm, &device);
  VpiHandle reached_out = vpi_handle(vpiOutTerm, &device);
  EXPECT_EQ(reached_in, &in_term);
  EXPECT_EQ(reached_out, &out_term);

  // The handles returned for the terminals have the delay term type.
  EXPECT_EQ(vpi_get(vpiType, reached_in), vpiDelayTerm);
  EXPECT_EQ(vpi_get(vpiType, reached_out), vpiDelayTerm);
}

// vpiInTerm / vpiOutTerm (edge): a delay device that has no designated terminal
// reports a null handle rather than reaching a stray object.
TEST_F(DelayTerminals, TermRelationsAreNullWhenAbsent) {
  VpiObject device;
  device.type = vpiDelayDevice;
  // in_term and out_term left null.

  EXPECT_EQ(vpi_handle(vpiInTerm, &device), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, &device), nullptr);
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

  EXPECT_EQ(vpi_handle(vpiInTerm, &not_a_device), nullptr);
  EXPECT_EQ(vpi_handle(vpiOutTerm, &not_a_device), nullptr);
}

// vpiDelayType: a delay device and a delay term both report their delay-type
// code through vpi_get(vpiDelayType); an object that is neither reports zero.
TEST_F(DelayTerminals, DelayTypeIsReported) {
  VpiObject device;
  device.type = vpiDelayDevice;
  device.delay_type = 3;
  EXPECT_EQ(vpi_get(vpiDelayType, &device), 3);

  VpiObject term;
  term.type = vpiDelayTerm;
  term.delay_type = 5;
  EXPECT_EQ(vpi_get(vpiDelayType, &term), 5);

  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiDelayType, &other), 0);
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
  EXPECT_EQ(vpi_handle(vpiModule, &device), &module_scope);

  VpiObject orphan;
  orphan.type = vpiDelayDevice;
  EXPECT_EQ(vpi_handle(vpiModule, &orphan), nullptr);
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
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;  // a variable driver, not a net driver

  VpiObject in_term;
  in_term.type = vpiDelayTerm;
  in_term.children = {&prim_term, &assign_stmt};

  vpiHandle itr = vpi_iterate(vpiDriver, &in_term);
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(vpi_scan(itr), &prim_term);
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

  vpiHandle itr = vpi_iterate(vpiLoad, &out_term);
  ASSERT_NE(itr, nullptr);
  EXPECT_EQ(vpi_scan(itr), &assign_stmt);
  EXPECT_EQ(vpi_scan(itr), nullptr);
}

}  // namespace
}  // namespace delta
