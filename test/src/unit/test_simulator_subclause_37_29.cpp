#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &iface);
}

// D1: a virtual interface var whose declaration assigned no interface reports
// NULL for vpiExpr rather than reaching some unrelated child.
TEST_F(VirtualInterface, ExprIsNullWhenNoInterfaceAssigned) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;  // no children -> no assignment

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&vif)), nullptr);
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
TEST_F(VirtualInterface, ExprSkipsRefObjWhoseActualIsNotAnInterface) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject ref_to_net;  // bound to a net, not an interface/modport
  ref_to_net.type = vpiRefObj;
  ref_to_net.actual = &net;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&ref_to_net};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&vif)), nullptr);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &modport);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &source_vif);
}

// D1 + D2 (ref-obj operand, accepting form): the figure's vpiExpr group admits
// a ref obj, and detail 2 makes it legal when its vpiActual is an interface
// passed through a port. Such a ref obj is handed back by vpiExpr - the
// accepting counterpart to ExprSkipsRefObjWhoseActualIsNotAnInterface.
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &ref_to_iface);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &null_const);
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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&vif))), &iface);
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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&vif))), &modport);
}

// Example 2: vpiActual returns NULL while the virtual interface is
// uninitialized - queried before any assignment has bound it.
TEST_F(VirtualInterface, ActualIsNullWhileUninitialized) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;  // no actual bound yet

  EXPECT_EQ(vpi_handle(vpiActual, VpiHandleOf(&vif)), nullptr);
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

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&vif)), "bus");
  EXPECT_STREQ(vpi_get_str(vpiFullName, VpiHandleOf(&vif)),
               "SBusTransactor.bus");
  EXPECT_EQ(vpi_get(vpiIsModPort, VpiHandleOf(&vif)), 0);
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

  EXPECT_EQ(vpi_get(vpiIsModPort, VpiHandleOf(&vif)), 1);
}

// D1: the assignment is the first child of an interface-expr kind, so a child
// of another kind written before it is passed over rather than handed back.
TEST_F(VirtualInterface, ExprPassesOverAChildOfAnotherKind) {
  VpiObject typespec;
  typespec.type = vpiInterfaceTypespec;
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&typespec, &iface};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &iface);
}

// §37.29 against a design read and run whole.
class VirtualInterfaceVarsOfARun : public VpiDesignRun {
 protected:
  // The virtual interface var `name` the class obj top.c holds.
  static vpiHandle ObjectsVar(const char* name) {
    return Named(vpiVirtualInterfaceVar, vpi_handle(vpiClassObj, By("top.c")),
                 name);
  }
};

constexpr const char* kVirtualInterfaces =
    "interface SBus; logic req; modport phy(input req); endinterface\n"
    "class C;\n"
    "  virtual SBus cv;\n"
    "  virtual SBus.phy cp;\n"
    "  function new(virtual SBus b); cv = b; endfunction\n"
    "endclass\n"
    "module top;\n"
    "  SBus bus();\n"
    "  virtual SBus v = bus;\n"
    "  virtual SBus.phy p;\n"
    "  virtual SBus w;\n"
    "  C c;\n"
    "  initial begin w = bus; c = new(bus); end\n"
    "endmodule\n";

// §37.29 with §37.30: a module's virtual interface var reaches through
// vpiTypespec the interface typespec of the type it was declared with, a
// modport's for one naming a modport (#7115).
TEST_F(VirtualInterfaceVarsOfARun, AVarReachesItsInterfaceTypespec) {
  Run(kVirtualInterfaces);
  vpiHandle of_v = vpi_handle(vpiTypespec, By("top.v"));
  ASSERT_NE(of_v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_v), vpiInterfaceTypespec);
  EXPECT_STREQ(vpi_get_str(vpiDefName, of_v), "SBus");
  vpiHandle of_p = vpi_handle(vpiTypespec, By("top.p"));
  ASSERT_NE(of_p, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiDefName, of_p), "phy");
  EXPECT_EQ(vpi_get(vpiIsModPort, of_p), 1);
}

// §37.29: a virtual interface var of a modport's type reports vpiIsModPort
// TRUE, in a module and in a class obj alike, and one of an interface's
// FALSE (#7117).
TEST_F(VirtualInterfaceVarsOfARun, AVarOfAModportTypeIsAModport) {
  Run(kVirtualInterfaces);
  EXPECT_EQ(vpi_get(vpiIsModPort, By("top.p")), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, By("top.v")), 0);
  EXPECT_EQ(vpi_get(vpiIsModPort, ObjectsVar("cp")), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, ObjectsVar("cv")), 0);
}

// §37.29 detail 1: vpiExpr reaches the interface instance a declaration
// assigns, and nothing for one it assigns none (#7118).
TEST_F(VirtualInterfaceVarsOfARun, AnInitializedVarReachesItsInstance) {
  Run(kVirtualInterfaces);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, By("top.v"))),
            VpiObjectOf(By("top.bus")));
  EXPECT_EQ(vpi_handle(vpiExpr, By("top.w")), nullptr);
}

// §37.29 example 2: vpiActual reaches the interface instance a var refers to
// once it is assigned one, in a module and in a class obj, and nothing for one
// never assigned (#7116).
TEST_F(VirtualInterfaceVarsOfARun, AnAssignedVarReachesWhatItRefersTo) {
  Run(kVirtualInterfaces);
  vpiHandle bus = By("top.bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, By("top.w"))), VpiObjectOf(bus));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, By("top.v"))), VpiObjectOf(bus));
  EXPECT_EQ(vpi_handle(vpiActual, By("top.p")), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, ObjectsVar("cv"))),
            VpiObjectOf(bus));
}

}  // namespace
}  // namespace delta
