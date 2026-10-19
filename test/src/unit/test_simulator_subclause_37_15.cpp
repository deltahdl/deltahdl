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

// §37.15 Reference objects: the VPI ref obj object model. A ref obj stands in
// for a declared object (or a subelement of one) that references an actual
// instantiated object - for instance the lowConn of an interface port (§37.14
// detail 5). Details 1, 2 are descriptive of when/what a ref obj is and carry
// no own decision rule; the rule-bearing details (3-7) are observed below
// against the production helpers and dispatch cases in vpi.cpp, and the ref
// objs a design's ports make are read back from a run (RefObjsOfARun).

class RefObjContext : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D3: the vpiActual relationship returns the actual instantiated object the ref
// obj is bound to, or NULL when it is not bound.
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

// The figure: a ref obj standing in no instance is the connection of no port.
TEST_F(RefObjContext, ARefObjInNoInstanceReachesNoPorts) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  EXPECT_EQ(vpi_iterate(vpiLowConn, VpiHandleOf(&ref_obj)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiPortInst, VpiHandleOf(&ref_obj)), nullptr);
}

// D4: vpiParent traverses from a ref obj that is a subelement of a ref obj up
// to its containing ref obj. Modelled on the clause's example: r[0] is a ref
// obj whose parent is the ref obj r; vpiActual of r[0] is the var bit a[0], and
// vpiActual of r is the variable a.
TEST_F(RefObjContext, ParentTraversesSubelementRefObj) {
  VpiObject var_a;  // variable a
  var_a.type = vpiReg;
  VpiObject var_bit_a0;  // var bit a[0]
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

// D5: vpiGeneric is TRUE for a reference to a generic interface, FALSE for a
// reference to a non-generic interface, and vpiUndefined for any other ref obj.
TEST_F(RefObjContext, GenericPropertyByReferenceKind) {
  EXPECT_EQ(VpiRefObjGeneric(/*refers_to_interface=*/true,
                             /*is_generic_interface=*/true),
            1);
  EXPECT_EQ(VpiRefObjGeneric(/*refers_to_interface=*/true,
                             /*is_generic_interface=*/false),
            0);
  EXPECT_EQ(VpiRefObjGeneric(/*refers_to_interface=*/false,
                             /*is_generic_interface=*/false),
            vpiUndefined);

  // A ref obj to a generic interface.
  VpiObject generic_iface;
  generic_iface.type = vpiInterface;
  VpiObject generic_ref;
  generic_ref.type = vpiRefObj;
  generic_ref.actual = &generic_iface;
  generic_ref.generic_interface = true;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&generic_ref)), 1);

  // A ref obj to a non-generic interface.
  VpiObject plain_iface;
  plain_iface.type = vpiInterface;
  VpiObject plain_ref;
  plain_ref.type = vpiRefObj;
  plain_ref.actual = &plain_iface;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&plain_ref)), 0);

  // A ref obj to something that is not an interface -> vpiUndefined.
  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&net_ref)), vpiUndefined);
}

// D5 (input form): an interface array is one of the vpiActual kinds the ref obj
// diagram admits, and a reference to it is still a reference to an interface,
// so vpiGeneric reports its generic-ness rather than vpiUndefined.
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

// D6: vpiDefName for a ref obj whose actual is an interface or modport returns
// that interface's definition name or the modport name; otherwise NULL.
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

  // A ref obj whose actual is a net is neither an interface nor a modport.
  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&net_ref)), nullptr);
}

// D6 (input form): an interface array actual - the third interface-bearing
// vpiActual kind in the ref obj diagram alongside the plain interface and the
// modport - reports its interface definition name through vpiDefName.
TEST_F(RefObjContext, DefNameForInterfaceArrayActual) {
  VpiObject iface_array;
  iface_array.type = vpiInterfaceArray;
  iface_array.name = "simple";
  VpiObject array_ref;
  array_ref.type = vpiRefObj;
  array_ref.actual = &iface_array;
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&array_ref)), "simple");
}

// D7: vpiTypespec returns NULL for a ref obj whose actual is not a net,
// variable, or part select; otherwise it returns the typespec that actual
// holds, one of the concrete kinds §37.25 defines.
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

  // A part-select actual also exposes the typespec.
  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.children.push_back(&typespec);
  VpiObject ps_ref;
  ps_ref.type = vpiRefObj;
  ps_ref.actual = &part_select;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&ps_ref))),
            &typespec);

  // An interface actual is none of net/variable/part select -> NULL, even
  // though it holds a typespec.
  VpiObject iface;
  iface.type = vpiInterface;
  iface.children.push_back(&typespec);
  VpiObject iface_ref;
  iface_ref.type = vpiRefObj;
  iface_ref.actual = &iface;
  EXPECT_EQ(VpiRefObjTypespec(&iface_ref), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&iface_ref)), nullptr);
}

// D7 (the variable arm, through the vpi_handle dispatch path): a ref obj whose
// actual is a variable - the third kind the rule admits alongside net and part
// select - exposes that variable's typespec.
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

// D5: vpiGeneric is drawn on the ref obj alone, and a ref obj bound to nothing
// refers to no interface, so both a net and an unbound ref obj report
// vpiUndefined.
TEST_F(RefObjContext, GenericPropertyOffABoundRefObjIsUndefined) {
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&net)), vpiUndefined);
  VpiObject unbound;
  unbound.type = vpiRefObj;
  EXPECT_EQ(vpi_get(vpiGeneric, VpiHandleOf(&unbound)), vpiUndefined);
}

// D6 and D7: a ref obj bound to nothing has no actual to take a definition
// name or a typespec from, so both are NULL.
TEST_F(RefObjContext, AnUnboundRefObjHasNoDefNameOrTypespec) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;

  EXPECT_EQ(VpiRefObjDefName(&ref_obj), nullptr);
  EXPECT_EQ(VpiRefObjTypespec(&ref_obj), nullptr);
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&ref_obj)), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&ref_obj)), nullptr);
}

// D7: every kind the nets and variables classes group carries a typespec, a
// net bit and a var bit among them, so a ref obj bound to any of them reaches
// the typespec its actual holds.
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

// D7: the typespec reached is the one the actual holds, found past any child
// of another kind; an actual holding none reaches NULL.
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

// What the ports of a run reach: the helpers the fixtures below read a
// design's ref objs with.
class RefObjRun : public VpiDesignRun {
 protected:
  // The port `name` of the instance `inst`.
  static vpiHandle PortOf(const char* inst, const char* name) {
    return Named(vpiPort, By(inst), name);
  }

  // What the port `name` of `inst` reaches through `relation`.
  static vpiHandle ConnOf(int relation, const char* inst, const char* name) {
    vpiHandle port = PortOf(inst, name);
    return port == nullptr ? nullptr : vpi_handle(relation, port);
  }

  // The modport `name` of the interface instance top.i.
  static VpiObject* ModportOfI(const char* name) {
    return VpiObjectOf(Named(vpiModport, By("top.i"), name));
  }

  // The objects of what `ref` reaches through `type`, in no order the clause
  // gives, so sorted.
  static std::vector<VpiObject*> Reached(int type, vpiHandle ref) {
    std::vector<VpiObject*> objects;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      objects.push_back(VpiObjectOf(obj));
    }
    std::ranges::sort(objects);
    return objects;
  }
};

// The ref objs of a run: those the clause's example makes passing an
// interface and its modports through ports, with a port selecting a modport in
// its declaration, a generic interface port, a port connected to an element
// of an interface array and a ref port beside them.
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

// §37.14 detail 5 with D1: an interface port's lower connection is the ref
// obj its io decl holds, bound to the interface instance it is connected to,
// or to the modport the connection or the port's declaration selects (#7050).
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

// D1 with D4's example: a ref port's lower connection is the ref obj its io
// decl holds, bound to the variable connected to it, and the port keeps a
// port bit per bit of that variable (#7051).
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

// D2 and the example: the higher connection of an interface port is a ref
// obj bound to the interface or modport written; within child1, the
// connection s is a use of child1's own ref obj, and s.initiator a ref obj
// that is a subelement of it (D4), bound to the modport (#7347).
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

// D2 with §23.3.2: a connection to an element of an array of interface
// instances is a ref obj bound to that element, which the port's own ref obj
// is bound to as well (#7348).
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

// D2 with §27.4: a connection written in a generate block of top to an
// interface instance is a ref obj bound to that instance, as one written in
// top itself is (#7352).
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

// The figure: a ref obj reaches through vpiLowConn the port it is the lower
// connection of, through vpiHighConn the ports it is the higher connection
// of, and through vpiPortInst those and the ports a subelement of it connects
// (#7052).
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

// The figure: the ref obj a connection makes in top reaches only the port it
// connects, not those the other connections to the same interface make, in
// top or in a generate block of top.
TEST_F(RefObjsOfARun, ARefObjReachesOnlyThePortsOfItsOwnConnections) {
  vpiHandle high = ConnOf(vpiHighConn, "top.i1", "s");
  ASSERT_NE(high, nullptr);
  const std::vector<VpiObject*> kOwn{VpiObjectOf(PortOf("top.i1", "s"))};
  EXPECT_EQ(Reached(vpiHighConn, high), kOwn);
  EXPECT_EQ(Reached(vpiPortInst, high), kOwn);
}

// The figure with D4: vpiParent reaches only the ref obj a subelement selects
// from, so the ref obj of a port, held by its io decl, has none (#7053).
TEST_F(RefObjsOfARun, ARefObjOfAPortHasNoParent) {
  EXPECT_EQ(vpi_handle(vpiParent, ConnOf(vpiLowConn, "top.i1", "s")), nullptr);
  EXPECT_EQ(vpi_handle(vpiParent, ConnOf(vpiLowConn, "top.u1", "r")), nullptr);
}

// D5: the ref obj of a port declared with the interface keyword refers to a
// generic interface, that of one naming its interface to one that is not, and
// that of a ref port to no interface at all (#7054).
TEST_F(RefObjsOfARun, VpiGenericFollowsThePortsDeclaration) {
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.u4", "s")), 1);
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.i1", "s")), 0);
  EXPECT_EQ(vpi_get(vpiGeneric, ConnOf(vpiLowConn, "top.u1", "r")),
            vpiUndefined);
}

// D6: a ref obj bound to an interface reports the interface's definition
// name, not the instance's, and one bound to a modport the modport's name
// (#7055).
TEST_F(RefObjsOfARun, VpiDefNameIsTheInterfacesDefinitionOrTheModport) {
  EXPECT_STREQ(vpi_get_str(vpiDefName, ConnOf(vpiLowConn, "top.i1", "s")),
               "simple");
  EXPECT_STREQ(vpi_get_str(vpiDefName, ConnOf(vpiLowConn, "top.i2", "s")),
               "initiator");
}

// The figure with D7: a ref obj bound to a variable reaches that variable's
// typespec, here its typedef's, and one bound to an interface none (#7056).
TEST_F(RefObjsOfARun, VpiTypespecIsTheVariablesForAVariableActual) {
  vpiHandle typespec =
      vpi_handle(vpiTypespec, ConnOf(vpiLowConn, "top.u1", "q"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(VpiObjectOf(typespec),
            VpiObjectOf(vpi_handle(vpiTypespec, By("top.b"))));
  EXPECT_EQ(vpi_handle(vpiTypespec, ConnOf(vpiLowConn, "top.i1", "s")),
            nullptr);
}

// The ref objs of a run in which a module passes its interface port down to an
// instance a generate block of it holds.
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

// §25.3 with §27.4 and D2: an interface port passed into a generate block is
// the higher connection of the port it reaches there, whose own ref obj is
// bound to the interface the module is connected to (#7351).
TEST_F(RefObjsThroughAGenerateBlock, AnInterfacePortReachesThePortInTheBlock) {
  vpiHandle s = ConnOf(vpiLowConn, "top.i7", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VpiObjectOf(ConnOf(vpiHighConn, "top.i7.gb.c_g", "s")),
            VpiObjectOf(s));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual,
                                   ConnOf(vpiLowConn, "top.i7.gb.c_g", "s"))),
            VpiObjectOf(By("top.i")));
}

// The ref objs of a run in which the instance a generate block holds passes
// the interface port it was given on to an instance of its own.
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

// §25.3 with D2: the port an instance in a generate block passes on is the
// higher connection of the port of its own instance (#7351).
TEST_F(RefObjsBelowAGenerateBlock, AnInterfacePortReachesThePortBelowTheBlock) {
  vpiHandle inner = ConnOf(vpiLowConn, "top.i7.gb.c_g", "s");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(VpiObjectOf(ConnOf(vpiHighConn, "top.i7.gb.c_g.c_1", "s")),
            VpiObjectOf(inner));
}

}  // namespace
}  // namespace delta
