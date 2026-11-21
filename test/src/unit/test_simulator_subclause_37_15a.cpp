#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class RefObjContext : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(RefObjContext, ActualReturnsBoundObject) {
  VpiObject variable;
  variable.type = vpiReg;

  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  ref_obj.actual = &variable;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&ref_obj))),
            &variable);

  VpiObject unbound;
  unbound.type = vpiRefObj;
  EXPECT_EQ(vpi_handle(vpiActual, VpiHandleOf(&unbound)), nullptr);
}

TEST_F(RefObjContext, ARefObjInNoInstanceReachesNoPorts) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  EXPECT_EQ(vpi_iterate(vpiLowConn, VpiHandleOf(&ref_obj)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiPortInst, VpiHandleOf(&ref_obj)), nullptr);
}

TEST_F(RefObjContext, PortsAreThoseItConnectsAndParentIsARefObjHoldingIt) {
  VpiObject m;
  m.type = vpiModule;
  VpiObject r;
  r.type = vpiRefObj;
  r.parent = &m;
  VpiObject net;
  net.type = vpiNet;

  VpiObject own;
  own.type = vpiPort;
  own.low_conn = &r;
  VpiObject other;
  other.type = vpiPort;
  other.low_conn = &net;
  VpiObject to_r;
  to_r.type = vpiPort;
  to_r.high_conn = &r;
  VpiObject to_net;
  to_net.type = vpiPort;
  to_net.high_conn = &net;
  VpiObject stranger;
  stranger.type = vpiRefObj;
  VpiObject to_stranger;
  to_stranger.type = vpiPort;
  to_stranger.high_conn = &stranger;
  VpiObject u;
  u.type = vpiModule;
  u.children = {&to_net, &to_stranger, &to_r};
  VpiObject block;
  block.type = vpiGenScope;
  block.children = {&u};
  VpiObject blocks;
  blocks.type = vpiGenScopeArray;
  blocks.children = {&block};
  m.children = {&own, &other, &blocks};

  EXPECT_EQ(VpiRefObjPorts(vpiLowConn, &r), std::vector<VpiHandle>{&own});
  EXPECT_EQ(VpiRefObjPorts(vpiHighConn, &r), std::vector<VpiHandle>{&to_r});
  EXPECT_EQ(VpiRefObjPorts(vpiPortInst, &r), std::vector<VpiHandle>{&to_r});

  VpiObject orphan;
  orphan.type = vpiRefObj;
  EXPECT_EQ(VpiRefObjParent(&orphan), nullptr);
}

TEST_F(RefObjContext, ParentTraversesSubelementRefObj) {
  VpiObject var_a;
  var_a.type = vpiReg;
  VpiObject var_bit_a0;
  var_bit_a0.type = vpiReg;

  VpiObject r;
  r.type = vpiRefObj;
  r.actual = &var_a;
  VpiObject r0;
  r0.type = vpiRefObj;
  r0.parent = &r;
  r0.actual = &var_bit_a0;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&r0))), &r);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&r0))), &var_bit_a0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, VpiHandleOf(&r))), &var_a);
}

TEST_F(RefObjContext, GenericPropertyByReferenceKind) {
  EXPECT_EQ(VpiRefObjGeneric(true, true), 1);
  EXPECT_EQ(VpiRefObjGeneric(true, false), 0);
  EXPECT_EQ(VpiRefObjGeneric(false, false), vpiUndefined);

  VpiObject generic_iface;
  generic_iface.type = vpiInterface;
  VpiObject generic_ref;
  generic_ref.type = vpiRefObj;
  generic_ref.actual = &generic_iface;
  generic_ref.generic_interface = true;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&generic_ref)), 1);

  VpiObject plain_iface;
  plain_iface.type = vpiInterface;
  VpiObject plain_ref;
  plain_ref.type = vpiRefObj;
  plain_ref.actual = &plain_iface;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&plain_ref)), 0);

  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&net_ref)), vpiUndefined);
}

TEST_F(RefObjContext, GenericPropertyForInterfaceArrayActual) {
  VpiObject generic_iface_array;
  generic_iface_array.type = vpiInterfaceArray;
  VpiObject generic_ref;
  generic_ref.type = vpiRefObj;
  generic_ref.actual = &generic_iface_array;
  generic_ref.generic_interface = true;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&generic_ref)), 1);

  VpiObject plain_iface_array;
  plain_iface_array.type = vpiInterfaceArray;
  VpiObject plain_ref;
  plain_ref.type = vpiRefObj;
  plain_ref.actual = &plain_iface_array;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&plain_ref)), 0);
}

TEST_F(RefObjContext, DefNameForInterfaceAndModportActual) {
  VpiObject iface;
  iface.type = vpiInterface;
  iface.name = "simple";
  VpiObject iface_ref;
  iface_ref.type = vpiRefObj;
  iface_ref.actual = &iface;
  EXPECT_STREQ(VpiRefObjDefName(&iface_ref), "simple");
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&iface_ref)), "simple");

  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "initiator";
  VpiObject modport_ref;
  modport_ref.type = vpiRefObj;
  modport_ref.actual = &modport;
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&modport_ref)), "initiator");

  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&net_ref)), nullptr);
}

TEST_F(RefObjContext, DefNameForInterfaceArrayActual) {
  VpiObject iface_array;
  iface_array.type = vpiInterfaceArray;
  iface_array.name = "simple";
  VpiObject array_ref;
  array_ref.type = vpiRefObj;
  array_ref.actual = &iface_array;
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&array_ref)), "simple");
}

TEST_F(RefObjContext, TypespecGatedOnActualKind) {
  VpiObject typespec;
  typespec.type = vpiLogicTypespec;

  VpiObject net;
  net.type = vpiNet;
  net.children.push_back(&typespec);
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(VpiRefObjTypespec(&net_ref), &typespec);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&net_ref))),
            &typespec);

  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.children.push_back(&typespec);
  VpiObject ps_ref;
  ps_ref.type = vpiRefObj;
  ps_ref.actual = &part_select;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&ps_ref))),
            &typespec);

  VpiObject iface;
  iface.type = vpiInterface;
  iface.children.push_back(&typespec);
  VpiObject iface_ref;
  iface_ref.type = vpiRefObj;
  iface_ref.actual = &iface;
  EXPECT_EQ(VpiRefObjTypespec(&iface_ref), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&iface_ref)), nullptr);
}

TEST_F(RefObjContext, TypespecExposedForVariableActual) {
  VpiObject typespec;
  typespec.type = vpiIntegerTypespec;

  VpiObject variable;
  variable.type = vpiIntegerVar;
  variable.children.push_back(&typespec);
  VpiObject var_ref;
  var_ref.type = vpiRefObj;
  var_ref.actual = &variable;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&var_ref))),
            &typespec);
}

TEST_F(RefObjContext, GenericPropertyOffABoundRefObjIsUndefined) {
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&net)), vpiUndefined);
  VpiObject unbound;
  unbound.type = vpiRefObj;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&unbound)), vpiUndefined);
}

TEST_F(RefObjContext, AnUnboundRefObjHasNoDefNameOrTypespec) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;

  EXPECT_EQ(VpiRefObjDefName(&ref_obj), nullptr);
  EXPECT_EQ(VpiRefObjTypespec(&ref_obj), nullptr);
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&ref_obj)), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&ref_obj)), nullptr);
}

TEST_F(RefObjContext, EveryNetAndVariableActualExposesTheTypespec) {
  VpiObject typespec;
  typespec.type = vpiLogicTypespec;
  for (int kind :
       {vpiStructNet, vpiUnionNet, vpiEnumNet, vpiIntegerNet, vpiTimeNet,
        vpiBitNet, vpiPackedArrayNet, vpiNetArray, vpiNetBit, vpiReg,
        vpiIntegerVar, vpiRealVar, vpiIntVar, vpiBitVar, vpiStructVar,
        vpiEnumVar, vpiArrayVar, vpiVarBit}) {
    VpiObject actual;
    actual.type = kind;
    actual.children.push_back(&typespec);
    VpiObject ref_obj;
    ref_obj.type = vpiRefObj;
    ref_obj.actual = &actual;
    EXPECT_EQ(VpiRefObjTypespec(&ref_obj), &typespec) << kind;
  }
}

TEST_F(RefObjContext, TheTypespecIsFoundAmongOtherChildren) {
  VpiObject index;
  index.type = vpiConstant;
  VpiObject typespec;
  typespec.type = vpiLogicTypespec;
  VpiObject net;
  net.type = vpiNet;
  net.children = {&index, &typespec};
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  ref_obj.actual = &net;
  EXPECT_EQ(VpiRefObjTypespec(&ref_obj), &typespec);

  net.children = {&index};
  EXPECT_EQ(VpiRefObjTypespec(&ref_obj), nullptr);
}

class RefObjRun : public VpiDesignRun {
 protected:
  static vpiHandle PortOf(const char* inst, const char* name) {
    return Named(vpiPort, By(inst), name);
  }

  static vpiHandle ConnOf(int relation, const char* inst, const char* name) {
    vpiHandle port = PortOf(inst, name);
    return port == nullptr ? nullptr : vpi_handle(relation, port);
  }

  static VpiObject* ModportOfI(const char* name) {
    return VpiObjectOf(Named(vpiModport, By("top.i"), name));
  }

  static std::vector<VpiObject*> Reached(int type, vpiHandle ref) {
    std::vector<VpiObject*> objects;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      objects.push_back(VpiObjectOf(obj));
    }
    std::ranges::sort(objects);
    return objects;
  }
};

class RefObjsOfARun : public RefObjRun {
 protected:
  void SetUp() override {
    RefObjRun::SetUp();
    Run("interface simple (); logic req, gnt;\n"
        "  modport target (input req, output gnt);\n"
        "  modport initiator (input gnt, output req);\n"
        "endinterface\n"
        "module c1(simple s); endmodule\n"
        "module child1(simple s); c1 c_1(s); c1 c_2(s.initiator); endmodule\n"
        "module child2(simple s); endmodule\n"
        "module child3(simple.target t); endmodule\n"
        "module g(interface s); endmodule\n"
        "typedef logic [2:0] t3;\n"
        "module m(ref logic [2:0] r, ref t3 q); endmodule\n"
        "module top; simple i(); simple ia[2](); logic [2:0] a; t3 b;\n"
        "  child1 i1(i); child2 i2(i.initiator); child3 i3(i); g u4(i);\n"
        "  child2 i5(ia[1]); m u1(a, b);\n"
        "  if (1) begin : gb child2 i6(i); end\n"
        "endmodule\n");
  }
};

TEST_F(RefObjsOfARun, AnInterfacePortsLowConnIsARefObjBoundToItsInterface) {
  vpiHandle low = ConnOf(vpiLowConn, "top.i1", "s");
  ASSERT_NE(low, nullptr);
  EXPECT_EQ(vpi_get(vpiType, low), vpiRefObj);
  EXPECT_EQ(
      VpiObjectOf(low),
      VpiObjectOf(vpi_handle(vpiExpr, Named(vpiIODecl, By("top.i1"), "s"))));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, low)), VpiObjectOf(By("top.i")));
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiActual, ConnOf(vpiLowConn, "top.i2", "s"))),
      ModportOfI("initiator"));
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiActual, ConnOf(vpiLowConn, "top.i3", "t"))),
      ModportOfI("target"));
}

TEST_F(RefObjsOfARun, ARefPortsLowConnIsTheRefObjOfItsIoDecl) {
  vpiHandle low = ConnOf(vpiLowConn, "top.u1", "r");
  ASSERT_NE(low, nullptr);
  EXPECT_EQ(vpi_get(vpiType, low), vpiRefObj);
  EXPECT_EQ(
      VpiObjectOf(low),
      VpiObjectOf(vpi_handle(vpiExpr, Named(vpiIODecl, By("top.u1"), "r"))));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, low)), VpiObjectOf(By("top.a")));
  EXPECT_EQ(ObjectsOf(vpiBit, PortOf("top.u1", "r")).size(), 3U);
}

TEST_F(RefObjsOfARun, AnInterfacePortsHighConnIsARefObj) {
  vpiHandle i1 = ConnOf(vpiHighConn, "top.i1", "s");
  ASSERT_NE(i1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, i1), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, i1)), VpiObjectOf(By("top.i")));
  vpiHandle i2 = ConnOf(vpiHighConn, "top.i2", "s");
  ASSERT_NE(i2, nullptr);
  EXPECT_EQ(vpi_get(vpiType, i2), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, i2)), ModportOfI("initiator"));
  VpiObject* s = VpiObjectOf(ConnOf(vpiLowConn, "top.i1", "s"));
  EXPECT_EQ(VpiObjectOf(ConnOf(vpiHighConn, "top.i1.c_1", "s")), s);
  vpiHandle sub = ConnOf(vpiHighConn, "top.i1.c_2", "s");
  ASSERT_NE(sub, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sub), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, sub)), s);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, sub)), ModportOfI("initiator"));
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiActual, ConnOf(vpiLowConn, "top.i1.c_1", "s"))),
      VpiObjectOf(By("top.i")));
}

TEST_F(RefObjsOfARun, AConnectionToAnInterfaceArrayElementIsARefObj) {
  vpiHandle high = ConnOf(vpiHighConn, "top.i5", "s");
  ASSERT_NE(high, nullptr);
  EXPECT_EQ(vpi_get(vpiType, high), vpiRefObj);
  vpiHandle element = vpi_handle(vpiActual, high);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiInterface);
  EXPECT_STREQ(vpi_get_str(vpiFullName, element), "top.ia[1]");
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiActual, ConnOf(vpiLowConn, "top.i5", "s"))),
      VpiObjectOf(element));
}

TEST_F(RefObjsOfARun, AConnectionInAGenerateBlockIsARefObj) {
  vpiHandle inst = By("top.gb.i6");
  ASSERT_NE(inst, nullptr);
  vpiHandle port = PortOf("top.gb.i6", "s");
  ASSERT_NE(port, nullptr);
  EXPECT_NE(vpi_handle(vpiLowConn, port), nullptr);
  vpiHandle high = vpi_handle(vpiHighConn, port);
  ASSERT_NE(high, nullptr);
  EXPECT_EQ(vpi_get(vpiType, high), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, high)), VpiObjectOf(By("top.i")));
}

TEST_F(RefObjsOfARun, ARefObjReachesThePortsItConnects) {
  vpiHandle s = ConnOf(vpiLowConn, "top.i1", "s");
  ASSERT_NE(s, nullptr);
  VpiObject* own = VpiObjectOf(PortOf("top.i1", "s"));
  VpiObject* c_1 = VpiObjectOf(PortOf("top.i1.c_1", "s"));
  VpiObject* c_2 = VpiObjectOf(PortOf("top.i1.c_2", "s"));
  EXPECT_EQ(Reached(vpiLowConn, s), std::vector<VpiObject*>{own});
  EXPECT_EQ(Reached(vpiHighConn, s), std::vector<VpiObject*>{c_1});
  std::vector<VpiObject*> both{c_1, c_2};
  std::ranges::sort(both);
  EXPECT_EQ(Reached(vpiPortInst, s), both);
}

TEST_F(RefObjsOfARun, ARefObjReachesOnlyThePortsOfItsOwnConnections) {
  vpiHandle high = ConnOf(vpiHighConn, "top.i1", "s");
  ASSERT_NE(high, nullptr);
  const std::vector<VpiObject*> kOwn{VpiObjectOf(PortOf("top.i1", "s"))};
  EXPECT_EQ(Reached(vpiHighConn, high), kOwn);
  EXPECT_EQ(Reached(vpiPortInst, high), kOwn);
}

TEST_F(RefObjsOfARun, ARefObjOfAPortHasNoParent) {
  EXPECT_EQ(vpi_handle(vpiParent, ConnOf(vpiLowConn, "top.i1", "s")), nullptr);
  EXPECT_EQ(vpi_handle(vpiParent, ConnOf(vpiLowConn, "top.u1", "r")), nullptr);
}

TEST_F(RefObjsOfARun, VpiGenericFollowsThePortsDeclaration) {
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.u4", "s")), 1);
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.i1", "s")), 0);
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.u1", "r")),
            vpiUndefined);
}

TEST_F(RefObjsOfARun, VpiDefNameIsTheInterfacesDefinitionOrTheModport) {
  EXPECT_STREQ(vpi_get_str(vpiDefName, ConnOf(vpiLowConn, "top.i1", "s")),
               "simple");
  EXPECT_STREQ(vpi_get_str(vpiDefName, ConnOf(vpiLowConn, "top.i2", "s")),
               "initiator");
}

TEST_F(RefObjsOfARun, VpiTypespecIsTheVariablesForAVariableActual) {
  vpiHandle typespec =
      vpi_handle(vpiTypespec, ConnOf(vpiLowConn, "top.u1", "q"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(VpiObjectOf(typespec),
            VpiObjectOf(vpi_handle(vpiTypespec, By("top.b"))));
  EXPECT_EQ(vpi_handle(vpiTypespec, ConnOf(vpiLowConn, "top.i1", "s")),
            nullptr);
}

class RefObjsThroughAGenerateBlock : public RefObjRun {
 protected:
  void SetUp() override {
    RefObjRun::SetUp();
    Run("interface simple; logic req, gnt; endinterface\n"
        "module c1(simple s); endmodule\n"
        "module child4(simple s); if (1) begin : gb c1 c_g(s); end\n"
        "endmodule\n"
        "module top; simple i(); child4 i7(i); endmodule\n");
  }
};

TEST_F(RefObjsThroughAGenerateBlock, AnInterfacePortReachesThePortInTheBlock) {
  vpiHandle s = ConnOf(vpiLowConn, "top.i7", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VpiObjectOf(ConnOf(vpiHighConn, "top.i7.gb.c_g", "s")),
            VpiObjectOf(s));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual,
                                   ConnOf(vpiLowConn, "top.i7.gb.c_g", "s"))),
            VpiObjectOf(By("top.i")));
}

class RefObjsBelowAGenerateBlock : public RefObjRun {
 protected:
  void SetUp() override {
    RefObjRun::SetUp();
    Run("interface simple; logic req, gnt; endinterface\n"
        "module c1(simple s); endmodule\n"
        "module child1(simple s); c1 c_1(s); endmodule\n"
        "module child4(simple s); if (1) begin : gb child1 c_g(s); end\n"
        "endmodule\n"
        "module top; simple i(); child4 i7(i); endmodule\n");
  }
};

TEST_F(RefObjsBelowAGenerateBlock, AnInterfacePortReachesThePortBelowTheBlock) {
  vpiHandle inner = ConnOf(vpiLowConn, "top.i7.gb.c_g", "s");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(VpiObjectOf(ConnOf(vpiHighConn, "top.i7.gb.c_g.c_1", "s")),
            VpiObjectOf(inner));
}

class RefObjsOfFullPathConnections : public RefObjRun {
 protected:
  void SetUp() override {
    RefObjRun::SetUp();
    Run("interface simple (); logic req, gnt;\n"
        "  modport initiator (input gnt, output req);\n"
        "endinterface\n"
        "module child(simple s); endmodule\n"
        "module mid; child i3(top.i); endmodule\n"
        "module top; simple i();\n"
        "  child i1(top.i); child i2(top.i.initiator); mid md();\n"
        "endmodule\n");
  }
};

TEST_F(RefObjsOfFullPathConnections, AFullPathConnectionIsARefObj) {
  for (const char* inst : {"top.i1", "top.md.i3"}) {
    vpiHandle high = ConnOf(vpiHighConn, inst, "s");
    ASSERT_NE(high, nullptr) << inst;
    EXPECT_EQ(vpi_get(vpiType, high), vpiRefObj) << inst;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, high)),
              VpiObjectOf(By("top.i")))
        << inst;
  }
  vpiHandle i2 = ConnOf(vpiHighConn, "top.i2", "s");
  ASSERT_NE(i2, nullptr);
  EXPECT_EQ(vpi_get(vpiType, i2), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, i2)), ModportOfI("initiator"));
}

}  // namespace
}  // namespace delta
