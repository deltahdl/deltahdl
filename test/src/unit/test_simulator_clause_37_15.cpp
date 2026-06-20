#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.15 Reference objects: the VPI ref obj object model. A ref obj stands in
// for a declared object (or a subelement of one) that references an actual
// instantiated object - for instance the lowConn of an interface port (§37.14
// detail 5). Details 1, 2 are descriptive of when/what a ref obj is and carry
// no own decision rule; the rule-bearing details (3-7) are observed below
// against the production helpers and dispatch cases in vpi.cpp. The connection
// relations (vpiHighConn/vpiLowConn) are shared with §37.14 and tested there.

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
  EXPECT_EQ(VpiHandleC(vpiActual, &ref_obj), &variable);

  VpiObject unbound;
  unbound.type = vpiRefObj;
  EXPECT_EQ(VpiHandleC(vpiActual, &unbound), nullptr);
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

  EXPECT_EQ(VpiHandleC(vpiParent, &r0), &r);
  EXPECT_EQ(VpiHandleC(vpiActual, &r0), &var_bit_a0);
  EXPECT_EQ(VpiHandleC(vpiActual, &r), &var_a);
}

// D5: vpiGeneric is TRUE for a reference to a generic interface, FALSE for a
// reference to a non-generic interface, and vpiUndefined for any other ref obj.
TEST_F(RefObjContext, GenericPropertyByReferenceKind) {
  EXPECT_EQ(VpiRefObjGeneric(/*interface=*/true, /*generic=*/true), 1);
  EXPECT_EQ(VpiRefObjGeneric(/*interface=*/true, /*generic=*/false), 0);
  EXPECT_EQ(VpiRefObjGeneric(/*interface=*/false, /*generic=*/false),
            vpiUndefined);

  // A ref obj to a generic interface.
  VpiObject generic_iface;
  generic_iface.type = vpiInterface;
  VpiObject generic_ref;
  generic_ref.type = vpiRefObj;
  generic_ref.actual = &generic_iface;
  generic_ref.generic_interface = true;
  EXPECT_EQ(vpi_get(vpiGeneric, &generic_ref), 1);

  // A ref obj to a non-generic interface.
  VpiObject plain_iface;
  plain_iface.type = vpiInterface;
  VpiObject plain_ref;
  plain_ref.type = vpiRefObj;
  plain_ref.actual = &plain_iface;
  EXPECT_EQ(vpi_get(vpiGeneric, &plain_ref), 0);

  // A ref obj to something that is not an interface -> vpiUndefined.
  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get(vpiGeneric, &net_ref), vpiUndefined);
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
  EXPECT_STREQ(vpi_get_str(vpiDefName, &iface_ref), "simple");

  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "initiator";
  VpiObject modport_ref;
  modport_ref.type = vpiRefObj;
  modport_ref.actual = &modport;
  EXPECT_STREQ(vpi_get_str(vpiDefName, &modport_ref), "initiator");

  // A ref obj whose actual is a net is neither an interface nor a modport.
  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  EXPECT_EQ(vpi_get_str(vpiDefName, &net_ref), nullptr);
}

// D7: vpiTypespec returns NULL for a ref obj whose actual is not a net,
// variable, or part select; otherwise it returns the ref obj's typespec child.
TEST_F(RefObjContext, TypespecGatedOnActualKind) {
  VpiObject typespec;
  typespec.type = vpiTypespec;

  VpiObject net;
  net.type = vpiNet;
  VpiObject net_ref;
  net_ref.type = vpiRefObj;
  net_ref.actual = &net;
  net_ref.children.push_back(&typespec);
  EXPECT_EQ(VpiRefObjTypespec(&net_ref), &typespec);
  EXPECT_EQ(VpiHandleC(vpiTypespec, &net_ref), &typespec);

  // A part-select actual also exposes the typespec.
  VpiObject part_select;
  part_select.type = vpiPartSelect;
  VpiObject ps_ref;
  ps_ref.type = vpiRefObj;
  ps_ref.actual = &part_select;
  ps_ref.children.push_back(&typespec);
  EXPECT_EQ(VpiHandleC(vpiTypespec, &ps_ref), &typespec);

  // An interface actual is none of net/variable/part select -> NULL, even
  // though a typespec child is present.
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject iface_ref;
  iface_ref.type = vpiRefObj;
  iface_ref.actual = &iface;
  iface_ref.children.push_back(&typespec);
  EXPECT_EQ(VpiRefObjTypespec(&iface_ref), nullptr);
  EXPECT_EQ(VpiHandleC(vpiTypespec, &iface_ref), nullptr);
}

// D7 (the variable arm, through the vpi_handle dispatch path): a ref obj whose
// actual is a variable - the third kind the rule admits alongside net and part
// select - exposes its typespec child.
TEST_F(RefObjContext, TypespecExposedForVariableActual) {
  VpiObject typespec;
  typespec.type = vpiTypespec;

  VpiObject variable;
  variable.type = vpiIntegerVar;
  VpiObject var_ref;
  var_ref.type = vpiRefObj;
  var_ref.actual = &variable;
  var_ref.children.push_back(&typespec);
  EXPECT_EQ(VpiHandleC(vpiTypespec, &var_ref), &typespec);
}

}  // namespace
}  // namespace delta
