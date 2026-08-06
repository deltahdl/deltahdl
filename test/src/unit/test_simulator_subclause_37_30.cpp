#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.30 Interface typespec: an interface typespec (vpiInterfaceTypespec) is a
// typespec object that denotes a virtual interface or one of its modports.
// These tests observe the production code that applies the clause's two
// numbered "Details" - what vpiDefName reports for a modport versus an
// interface typespec (detail 1) and where vpiParent leads for each (detail 2) -
// together with the figure's vpiIsModPort/vpiName properties and the
// vpiParamAssign relation, which the generic Get/GetStr/Handle/Iterate
// machinery serves once the typespec's fields and children are populated.

// The fixture installs a context so the public vpi_get/vpi_get_str/vpi_handle/
// vpi_iterate entry points run their real dispatch over the test objects.
class InterfaceTypespec : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// §37.30: an interface typespec belongs to the typespec class (§37.25), so the
// typespec-class predicate recognizes it.
TEST_F(InterfaceTypespec, IsATypespec) {
  EXPECT_TRUE(VpiIsTypespecType(vpiInterfaceTypespec));
}

// D1: the vpiDefName of an interface typespec that represents a modport is the
// modport identifier. Observed both through the helper and the public
// vpi_get_str(vpiDefName) dispatch path.
TEST_F(InterfaceTypespec, DefNameOfModportIsModportIdentifier) {
  VpiObject modport_ts;
  modport_ts.type = vpiInterfaceTypespec;
  modport_ts.is_modport = true;
  modport_ts.def_name = "phy";  // the modport's identifier

  EXPECT_STREQ(VpiInterfaceTypespecDefName(&modport_ts), "phy");
  EXPECT_STREQ(vpi_get_str(vpiDefName, &modport_ts), "phy");
}

// D1: the vpiDefName of an interface typespec that represents an interface is
// the identifier of the interface declaration - SBus in the figure's example,
// where the typespec's own vpiName is the typedef name SB16.
TEST_F(InterfaceTypespec, DefNameOfInterfaceIsInterfaceDeclarationIdentifier) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;
  iface_ts.name = "SB16";      // the typedef name -> vpiName
  iface_ts.def_name = "SBus";  // the interface declaration's identifier

  EXPECT_STREQ(VpiInterfaceTypespecDefName(&iface_ts), "SBus");
  EXPECT_STREQ(vpi_get_str(vpiDefName, &iface_ts), "SBus");
  // The typedef name is the typespec's vpiName, distinct from the def name.
  EXPECT_STREQ(vpi_get_str(vpiName, &iface_ts), "SB16");
}

// D1 edge: the def-name helper only speaks for an interface typespec; any other
// handle (or a null handle) reports no definition name through it.
TEST_F(InterfaceTypespec, DefNameHelperOnlyForInterfaceTypespec) {
  VpiObject not_a_typespec;
  not_a_typespec.type = vpiStructTypespec;
  not_a_typespec.def_name = "ignored";

  EXPECT_EQ(VpiInterfaceTypespecDefName(&not_a_typespec), nullptr);
  EXPECT_EQ(VpiInterfaceTypespecDefName(nullptr), nullptr);
}

// D1 edge: an interface typespec with no recorded definition name reports NULL
// for vpiDefName rather than an empty string - the empty-name branch of the
// def-name dispatch, distinct from the wrong-kind guard above.
TEST_F(InterfaceTypespec, DefNameOfInterfaceTypespecWithoutRecordedNameIsNull) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.name = "SB16";  // has a vpiName, but no definition name recorded

  EXPECT_EQ(VpiInterfaceTypespecDefName(&iface_ts), nullptr);
  EXPECT_EQ(vpi_get_str(vpiDefName, &iface_ts), nullptr);
}

// D2: for an interface typespec that represents a modport, vpiParent returns
// the interface typespec of the corresponding interface. Observed through the
// helper and the public vpi_handle(vpiParent, ...) dispatch path.
TEST_F(InterfaceTypespec, ParentOfModportIsItsInterfaceTypespec) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;

  VpiObject modport_ts;
  modport_ts.type = vpiInterfaceTypespec;
  modport_ts.is_modport = true;
  modport_ts.parent = &iface_ts;

  EXPECT_EQ(VpiInterfaceTypespecParent(&modport_ts), &iface_ts);
  EXPECT_EQ(vpi_handle(vpiParent, &modport_ts), &iface_ts);
}

// D2: for an interface typespec that represents an interface, vpiParent returns
// NULL - even when some enclosing object is recorded as its parent pointer.
TEST_F(InterfaceTypespec, ParentOfInterfaceIsNull) {
  VpiObject enclosing;
  enclosing.type = vpiModule;

  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;
  iface_ts.parent =
      &enclosing;  // an interface typespec still reports no parent

  EXPECT_EQ(VpiInterfaceTypespecParent(&iface_ts), nullptr);
  EXPECT_EQ(vpi_handle(vpiParent, &iface_ts), nullptr);
}

// D2 edge: the parent helper only speaks for an interface typespec; any other
// handle (or a null handle) reports no parent through it.
TEST_F(InterfaceTypespec, ParentHelperOnlyForInterfaceTypespec) {
  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiInterfaceTypespecParent(&other), nullptr);
  EXPECT_EQ(VpiInterfaceTypespecParent(nullptr), nullptr);
}

// Figure property: vpi_get(vpiIsModPort) reports TRUE for a modport interface
// typespec and FALSE for one representing an interface.
TEST_F(InterfaceTypespec, IsModPortProperty) {
  VpiObject modport_ts;
  modport_ts.type = vpiInterfaceTypespec;
  modport_ts.is_modport = true;

  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;

  EXPECT_EQ(vpi_get(vpiIsModPort, &modport_ts), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, &iface_ts), 0);
}

// Figure relation: an interface typespec reaches its param assigns through the
// vpiParamAssign relation - the typedef SB16's assigned parameter value of 16
// in the figure's example is one such param assign, walked by
// vpi_iterate/vpi_scan.
TEST_F(InterfaceTypespec, ParamAssignIterationWalksParamAssigns) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;

  VpiObject pa_width;  // parameter WIDTH = 16
  pa_width.type = vpiParamAssign;
  VpiObject pa_other;  // a second parameter assignment
  pa_other.type = vpiParamAssign;
  iface_ts.children = {&pa_width, &pa_other};

  vpiHandle iter = vpi_iterate(vpiParamAssign, &iface_ts);
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);
}

// Figure relation, empty input form: an interface typespec for a parameterless
// interface (the typedef of an "interface SBus; ... endinterface" with no
// parameter port list) has no param assigns, so the vpiParamAssign relation has
// zero targets and vpi_iterate reports a null iterator rather than an empty
// one. A non-param-assign child is present to confirm the walk filters by kind
// rather than simply reporting whatever children exist.
TEST_F(InterfaceTypespec, ParamAssignIterationOfParameterlessInterfaceIsNull) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;

  VpiObject unrelated;  // a child of some other kind, never a param assign
  unrelated.type = vpiModport;
  iface_ts.children = {&unrelated};

  EXPECT_EQ(vpi_iterate(vpiParamAssign, &iface_ts), nullptr);
}

}  // namespace
}  // namespace delta
