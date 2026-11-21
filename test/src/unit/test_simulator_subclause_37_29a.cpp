#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VirtualInterface : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(VirtualInterface, InterfaceExprGroupMembership) {
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiInterface));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiModport));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiVirtualInterfaceVar));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsInterfaceExprType(vpiConstant));
  EXPECT_FALSE(VpiIsInterfaceExprType(vpiModule));
}

TEST_F(VirtualInterface, ExprReachesAssignedInterfaceInstance) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&iface};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &iface);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &iface);
}

TEST_F(VirtualInterface, ExprIsNullWhenNoInterfaceAssigned) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&vif)), nullptr);
}

TEST_F(VirtualInterface, ExprHelperOnlyForVirtualInterfaceVar) {
  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiVirtualInterfaceExpr(&other), nullptr);
  EXPECT_EQ(VpiVirtualInterfaceExpr(nullptr), nullptr);
}

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
  ref_unbound.type = vpiRefObj;

  EXPECT_TRUE(VpiInterfaceExprIsValid(&ref_to_iface));
  EXPECT_TRUE(VpiInterfaceExprIsValid(&ref_to_modport));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&ref_to_net));
  EXPECT_FALSE(VpiInterfaceExprIsValid(&ref_unbound));
}

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

TEST_F(VirtualInterface, ExprSkipsRefObjWhoseActualIsNotAnInterface) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject ref_to_net;
  ref_to_net.type = vpiRefObj;
  ref_to_net.actual = &net;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&ref_to_net};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&vif)), nullptr);
}

TEST_F(VirtualInterface, ExprReachesAssignedModport) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&modport};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &modport);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &modport);
}

TEST_F(VirtualInterface, ExprReachesAssignedNestedVirtualInterface) {
  VpiObject source_vif;
  source_vif.type = vpiVirtualInterfaceVar;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&source_vif};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &source_vif);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &source_vif);
}

TEST_F(VirtualInterface, ExprReachesAssignedRefObjPassedThroughPort) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject ref_to_iface;
  ref_to_iface.type = vpiRefObj;
  ref_to_iface.actual = &iface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.children = {&ref_to_iface};

  EXPECT_EQ(VpiVirtualInterfaceExpr(&vif), &ref_to_iface);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&vif))), &ref_to_iface);
}

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

TEST_F(VirtualInterface, ActualReachesHeldInterfaceInstance) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.actual = &iface;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&vif))), &iface);
}

TEST_F(VirtualInterface, ActualReachesHeldModport) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.is_modport = true;
  vif.actual = &modport;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&vif))), &modport);
}

TEST_F(VirtualInterface, ActualIsNullWhileUninitialized) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;

  EXPECT_EQ(vpi_handle(vpiActual, VpiHandleOf(&vif)), nullptr);
}

TEST_F(VirtualInterface, ActualWithNoRunIsTheInstanceTheVarWasBuiltHolding) {
  VpiObject iface;
  iface.type = vpiInterface;

  Variable storage;
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.var = &storage;
  vif.actual = &iface;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&vif))), &iface);
}

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

TEST_F(VirtualInterface, IsModPortTrueForModportQualifiedVar) {
  VpiObject vif;
  vif.type = vpiVirtualInterfaceVar;
  vif.name = "V32_Array";
  vif.is_modport = true;

  EXPECT_EQ(vpi_get(vpiIsModPort, VpiHandleOf(&vif)), 1);
}

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

class VirtualInterfaceVarsOfARun : public VpiDesignRun {
 protected:
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

TEST_F(VirtualInterfaceVarsOfARun, AVarOfAModportTypeIsAModport) {
  Run(kVirtualInterfaces);
  EXPECT_EQ(vpi_get(vpiIsModPort, By("top.p")), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, By("top.v")), 0);
  EXPECT_EQ(vpi_get(vpiIsModPort, ObjectsVar("cp")), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, ObjectsVar("cv")), 0);
}

TEST_F(VirtualInterfaceVarsOfARun, AnInitializedVarReachesItsInstance) {
  Run(kVirtualInterfaces);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, By("top.v"))),
            VpiObjectOf(By("top.bus")));
  EXPECT_EQ(vpi_handle(vpiExpr, By("top.w")), nullptr);
}

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
