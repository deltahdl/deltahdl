#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&modport_ts)), "phy");
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
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&iface_ts)), "SBus");
  // The typedef name is the typespec's vpiName, distinct from the def name.
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&iface_ts)), "SB16");
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
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&iface_ts)), nullptr);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&modport_ts))),
            &iface_ts);
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
  EXPECT_EQ(vpi_handle(vpiParent, VpiHandleOf(&iface_ts)), nullptr);
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

  EXPECT_EQ(vpi_get(vpiIsModPort, VpiHandleOf(&modport_ts)), 1);
  EXPECT_EQ(vpi_get(vpiIsModPort, VpiHandleOf(&iface_ts)), 0);
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

  vpiHandle iter = vpi_iterate(vpiParamAssign, VpiHandleOf(&iface_ts));
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

  EXPECT_EQ(vpi_iterate(vpiParamAssign, VpiHandleOf(&iface_ts)), nullptr);
}

// §37.30 against designs read and run whole.
class InterfaceTypespecsOfARun : public VpiDesignRun {
 protected:
  // The integer value of `obj`, -1 where nothing is written.
  static int IntValueOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    if (obj != nullptr) vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // The name each param assign `typespec` reaches assigns, with the kind of
  // what it assigns, in the order reached.
  static std::vector<std::pair<std::string, int>> Assigned(vpiHandle typespec) {
    std::vector<std::pair<std::string, int>> assigned;
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      vpiHandle rhs = vpi_handle(vpiRhs, assign);
      assigned.emplace_back(vpi_get_str(vpiName, vpi_handle(vpiLhs, assign)),
                            rhs == nullptr ? 0 : vpi_get(vpiType, rhs));
    }
    return assigned;
  }
};

constexpr const char* kSBus =
    "interface SBus #(parameter WIDTH = 8, parameter type T = logic);\n"
    "  logic req, grant;\n"
    "  logic [WIDTH-1:0] addr, data;\n"
    "  modport phy(input addr, inout data);\n"
    "endinterface\n"
    "module top;\n"
    "  parameter SIZE = 4;\n"
    "  typedef virtual SBus#(16) SB16;\n"
    "  typedef virtual SBus#(32).phy SBphy [1:SIZE];\n"
    "  typedef virtual SBus#(.T(byte)) SBbyte;\n"
    "  SBus #(16) bus();\n"
    "endmodule\n";

// §37.30 detail 3: a typedef of a virtual interface is an interface typespec
// named after the typedef, reporting the interface's name, assigning the
// parameter value it writes, 16, and reaching no parent (details 1 and 2), and
// vpiTypedef of the module reaches it beside the array typedef (#7120).
TEST_F(InterfaceTypespecsOfARun,
       AVirtualInterfaceTypedefIsAnInterfaceTypespec) {
  Run(kSBus);
  vpiHandle sb16 = Named(vpiTypedef, By("top"), "SB16");
  ASSERT_NE(sb16, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sb16), vpiInterfaceTypespec);
  EXPECT_STREQ(vpi_get_str(vpiDefName, sb16), "SBus");
  EXPECT_EQ(vpi_get(vpiIsModPort, sb16), 0);
  EXPECT_EQ(vpi_handle(vpiParent, sb16), nullptr);
  const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiParamAssign, sb16);
  ASSERT_EQ(kAssigns.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, kAssigns[0])), "WIDTH");
  EXPECT_EQ(IntValueOf(vpi_handle(vpiRhs, kAssigns[0])), 16);
  EXPECT_NE(Named(vpiTypedef, By("top"), "SBphy"), nullptr);
}

// §37.30 details 1 to 3: SBphy is an array typespec whose element is the
// typespec of the modport phy, reporting the modport's name and reaching
// through vpiParent an interface typespec of SBus, which assigns 32 (#7120).
TEST_F(InterfaceTypespecsOfARun, AModportTypespecReachesItsInterfaces) {
  Run(kSBus);
  vpiHandle phy_array = Named(vpiTypedef, By("top"), "SBphy");
  ASSERT_NE(phy_array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, phy_array), vpiArrayTypespec);
  vpiHandle phy = vpi_handle(vpiElemTypespec, phy_array);
  ASSERT_NE(phy, nullptr);
  EXPECT_EQ(vpi_get(vpiType, phy), vpiInterfaceTypespec);
  EXPECT_STREQ(vpi_get_str(vpiDefName, phy), "phy");
  EXPECT_EQ(vpi_get(vpiIsModPort, phy), 1);
  vpiHandle sbus = vpi_handle(vpiParent, phy);
  ASSERT_NE(sbus, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiDefName, sbus), "SBus");
  const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiParamAssign, sbus);
  ASSERT_EQ(kAssigns.size(), 1U);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiRhs, kAssigns[0])), 32);
}

// §37.30 detail 3: a type given a type parameter by name is assigned as the
// typespec of that type (#7120).
TEST_F(InterfaceTypespecsOfARun, ATypeGivenByNameIsAssignedItsTypespec) {
  Run(kSBus);
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("top"), "SBbyte")),
            (std::vector<std::pair<std::string, int>>{{"T", vpiByteTypespec}}));
}

}  // namespace
}  // namespace delta
