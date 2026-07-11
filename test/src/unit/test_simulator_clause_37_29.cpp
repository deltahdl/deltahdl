#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.29 Virtual interface: a virtual interface var (vpiVirtualInterfaceVar) is
// a variable that holds an interface instance. These tests observe the
// production code that applies the clause's two numbered "Details" - what
// vpiExpr reports for the declaration-time assignment (detail 1) and which
// objects may serve as an interface expr (detail 2) - together with the
// figure's vpiActual relation (refined by Example 2: NULL while uninitialized)
// and the vpiName/vpiFullName/vpiIsModPort properties served by the generic
// machinery.

// The fixture installs a context so the public vpi_get/vpi_get_str/vpi_handle
// entry points run their real dispatch over the test objects.
class VirtualInterface : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Figure ("interface expr" group): the interface-expr predicate recognizes an
// interface, a modport, a virtual interface var, a ref obj, and a constant, and
// rejects an unrelated kind.
TEST_F(VirtualInterface, InterfaceExprGroupMembership) {
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiInterface));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiModport));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiVirtualInterfaceVar));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiConstant));
  EXPECT_FALSE(VpiIsInterfaceExprType(vpiModule));
}

// D1: vpiExpr of a virtual interface var reaches the interface instance
// assigned in its declaration. Observed through the helper and the public
// vpi_handle(vpiExpr, ...) dispatch path.
TEST_F(VirtualInterface, ExprReachesAssignedInterfaceInstance) {
  VpiObject iface;  // the interface instance assigned at declaration
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&iface};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &iface);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), &iface);
}

// D1: a virtual interface var whose declaration assigned no interface reports
// NULL for vpiExpr rather than reaching some unrelated child.
TEST_F(VirtualInterface, ExprIsNullWhenNoInterfaceAssigned) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;  // no children -> no assignment

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), nullptr);
}

// D1 edge: the helper only speaks for a virtual interface var; any other handle
// (or a null handle) reports no expr through it.
TEST_F(VirtualInterface, ExprHelperOnlyForVirtualInterfaceVar) {
  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiVirtualInterfaceExpr(&other), nullptr);
  EXPECT_EQ(VpiVirtualInterfaceExpr(nullptr), nullptr);
}

// D2: a ref obj is a legal interface expr only when its vpiActual is an
// interface or a modport (a local declaration passed through a port).
TEST_F(VirtualInterface,
       RefObjIsInterfaceExprOnlyWhenActualIsInterfaceOrModport) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject modport;
  modport.type = vpiModport;
  VpiObject net;
  net.type = kVpiNet;

  VpiObject ref_to_iface;
  ref_to_iface.type = vpiRefObj;
  ref_to_iface.actual = &iface;
  VpiObject ref_to_modport;
  ref_to_modport.type = vpiRefObj;
  ref_to_modport.actual = &modport;
  VpiObject ref_to_net;
  ref_to_net.type = vpiRefObj;
  ref_to_net.actual = &net;
  VpiObject ref_unbound;
  ref_unbound.type = vpiRefObj;  // no actual

  EXPECT_TRUE(VpiInterfaceExprIsValid(&ref_to_iface));
  EXPECT_TRUE(VpiInterfaceExprIsValid(&ref_to_modport));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&ref_to_net));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&ref_unbound));
}

// D2: a constant is a legal interface expr only when its vpiConstType is
// vpiNullConst.
TEST_F(VirtualInterface, ConstantIsInterfaceExprOnlyWhenNullConst) {
  VpiObject null_const;
  null_const.type = vpiConstant;
  null_const.const_type = vpiNullConst;
  VpiObject int_const;
  int_const.type = vpiConstant;
  int_const.const_type = vpiIntConst;

  EXPECT_TRUE(VpiInterfaceExprIsValid(&null_const));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&int_const));
}

// D2: an interface, a modport, and a (nested) virtual interface var are always
// legal interface exprs; a null handle and any unrelated kind are not. Covers
// the always-valid arms of the validity predicate together with its null guard
// and its default-false branch.
TEST_F(VirtualInterface, InterfaceModportAndVifAreAlwaysValidInterfaceExprs) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject modport;
  modport.type = vpiModport;
  VpiObject nested_vif;
  nested_vif.type = vpiVirtualInterfaceVar;
  VpiObject unrelated;
  unrelated.type = vpiModule;

  EXPECT_TRUE(VpiInterfaceExprIsValid(&iface));
  EXPECT_TRUE(VpiInterfaceExprIsValid(&modport));
  EXPECT_TRUE(VpiInterfaceExprIsValid(&nested_vif));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&unrelated));
  EXPECT_FALSE(VpiInterfaceExprIsValid(nullptr));
}

// D1 + D2 together through the public path: a ref-obj assignment that fails the
// detail-2 constraint is not an interface expr, so vpiExpr does not hand it
// back.
TEST_F(VirtualInterface, ExprSkipsRefObjThatFailsDetail2) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject ref_to_net;  // bound to a net, not an interface/modport
  ref_to_net.type = vpiRefObj;
  ref_to_net.actual = &net;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&ref_to_net};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), nullptr);
}

// D1 (modport operand): the figure's vpiExpr group admits a modport, so a
// declaration that assigns a modport-qualified interface (e.g.
// "virtual SBus.phy bus = s") reaches that modport through vpiExpr.
TEST_F(VirtualInterface, ExprReachesAssignedModport) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&modport};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &modport);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), &modport);
}

// D1 (virtual-interface-var operand): the figure's vpiExpr group admits another
// virtual interface var, so a declaration that assigns one virtual interface to
// another (e.g. "virtual SBus bus = other") reaches that var through vpiExpr.
TEST_F(VirtualInterface, ExprReachesAssignedNestedVirtualInterface) {
  VpiObject source_vif;
  source_vif.type = vpiVirtualInterfaceVar;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&source_vif};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &source_vif);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), &source_vif);
}

// D1 + D2 (ref-obj operand, accepting form): the figure's vpiExpr group admits
// a ref obj, and detail 2 makes it legal when its vpiActual is an interface
// passed through a port. Such a ref obj is handed back by vpiExpr - the
// accepting counterpart to ExprSkipsRefObjThatFailsDetail2.
TEST_F(VirtualInterface, ExprReachesAssignedRefObjPassedThroughPort) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject ref_to_iface;  // a port-passed interface reference
  ref_to_iface.type = vpiRefObj;
  ref_to_iface.actual = &iface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&ref_to_iface};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &ref_to_iface);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), &ref_to_iface);
}

// D1 + D2 (constant operand): the figure's vpiExpr group admits a constant, and
// detail 2 makes it legal only as a null constant, so a declaration that
// assigns null (e.g. "virtual SBus bus = null") reaches that null constant
// through vpiExpr.
TEST_F(VirtualInterface, ExprReachesAssignedNullConstant) {
  VpiObject null_const;
  null_const.type = vpiConstant;
  null_const.const_type = vpiNullConst;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&null_const};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &null_const);
  EXPECT_EQ(vpi_handle(vpiExpr, &vif), &null_const);
}

// Example 2: vpiActual of a virtual interface var reaches the interface
// instance it currently holds - the actual passed to the new call that bound
// it.
TEST_F(VirtualInterface, ActualReachesHeldInterfaceInstance) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.actual = &iface;

  EXPECT_EQ(vpi_handle(vpiActual, &vif), &iface);
}

// Figure (vpiActual -> modport arm): a virtual interface var declared over a
// modport-qualified type (e.g. "virtual SBus.phy") holds a modport, so its
// vpiActual reaches a modport rather than a plain interface - the other target
// kind the figure admits for vpiActual, distinct from the interface form above.
TEST_F(VirtualInterface, ActualReachesHeldModport) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.is_modport = true;
  vif.actual = &modport;

  EXPECT_EQ(vpi_handle(vpiActual, &vif), &modport);
}

// Example 2: vpiActual returns NULL while the virtual interface is
// uninitialized - queried before any assignment has bound it.
TEST_F(VirtualInterface, ActualIsNullWhileUninitialized) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;  // no actual bound yet

  EXPECT_EQ(vpi_handle(vpiActual, &vif), nullptr);
}

// Figure properties: the virtual interface var carries vpiName/vpiFullName and
// a vpiIsModPort Boolean, reported by the generic Get/GetStr dispatch. Example
// 2's virtual interface var is named "bus".
TEST_F(VirtualInterface, NameAndIsModPortProperties) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.name = "bus";
  vif.full_name = "SBusTransactor.bus";
  vif.is_modport = false;

  EXPECT_STREQ(vpi_get_str(vpiName, &vif), "bus");
  EXPECT_STREQ(vpi_get_str(vpiFullName, &vif), "SBusTransactor.bus");
  EXPECT_EQ(vpi_get(vpiIsModPort, &vif), 0);
}

// Figure property (vpiIsModPort true arm): a virtual interface var declared
// over a modport-qualified type (e.g. "virtual SBus.phy") reports vpiIsModPort
// as true - the other value of the figure's Boolean, distinct from the
// interface form above.
TEST_F(VirtualInterface, IsModPortTrueForModportQualifiedVar) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.name = "V32_Array";
  vif.is_modport = true;

  EXPECT_EQ(vpi_get(vpiIsModPort, &vif), 1);
}

}  // namespace
}  // namespace delta
