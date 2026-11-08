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

class InterfaceTypespec : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(InterfaceTypespec, IsATypespec) {
  EXPECT_TRUE(VpiIsTypespecType(vpiInterfaceTypespec));
}

TEST_F(InterfaceTypespec, DefNameOfModportIsModportIdentifier) {
  VpiObject modport_ts;
  modport_ts.type = vpiInterfaceTypespec;
  modport_ts.is_modport = true;
  modport_ts.def_name = "phy";

  EXPECT_STREQ(VpiInterfaceTypespecDefName(&modport_ts), "phy");
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&modport_ts)), "phy");
}

TEST_F(InterfaceTypespec, DefNameOfInterfaceIsInterfaceDeclarationIdentifier) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;
  iface_ts.name = "SB16";
  iface_ts.def_name = "SBus";

  EXPECT_STREQ(VpiInterfaceTypespecDefName(&iface_ts), "SBus");
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(&iface_ts)), "SBus");
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&iface_ts)), "SB16");
}

TEST_F(InterfaceTypespec, DefNameHelperOnlyForInterfaceTypespec) {
  VpiObject not_a_typespec;
  not_a_typespec.type = vpiStructTypespec;
  not_a_typespec.def_name = "ignored";

  EXPECT_EQ(VpiInterfaceTypespecDefName(&not_a_typespec), nullptr);
  EXPECT_EQ(VpiInterfaceTypespecDefName(nullptr), nullptr);
}

TEST_F(InterfaceTypespec, DefNameOfInterfaceTypespecWithoutRecordedNameIsNull) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.name = "SB16";

  EXPECT_EQ(VpiInterfaceTypespecDefName(&iface_ts), nullptr);
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&iface_ts)), nullptr);
}

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

TEST_F(InterfaceTypespec, ParentOfInterfaceIsNull) {
  VpiObject enclosing;
  enclosing.type = vpiModule;

  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;
  iface_ts.is_modport = false;
  iface_ts.parent = &enclosing;

  EXPECT_EQ(VpiInterfaceTypespecParent(&iface_ts), nullptr);
  EXPECT_EQ(vpi_handle(vpiParent, VpiHandleOf(&iface_ts)), nullptr);
}

TEST_F(InterfaceTypespec, ParentHelperOnlyForInterfaceTypespec) {
  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiInterfaceTypespecParent(&other), nullptr);
  EXPECT_EQ(VpiInterfaceTypespecParent(nullptr), nullptr);
}

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

TEST_F(InterfaceTypespec, ParamAssignIterationWalksParamAssigns) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;

  VpiObject pa_width;
  pa_width.type = vpiParamAssign;
  VpiObject pa_other;
  pa_other.type = vpiParamAssign;
  iface_ts.children = {&pa_width, &pa_other};

  vpiHandle iter = vpi_iterate(vpiParamAssign, VpiHandleOf(&iface_ts));
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);
}

TEST_F(InterfaceTypespec, ParamAssignIterationOfParameterlessInterfaceIsNull) {
  VpiObject iface_ts;
  iface_ts.type = vpiInterfaceTypespec;

  VpiObject unrelated;
  unrelated.type = vpiModport;
  iface_ts.children = {&unrelated};

  EXPECT_EQ(vpi_iterate(vpiParamAssign, VpiHandleOf(&iface_ts)), nullptr);
}

class InterfaceTypespecsOfARun : public VpiDesignRun {
 protected:
  static int IntValueOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    if (obj != nullptr) vpi_get_value(obj, &value);
    return value.value.integer;
  }

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

TEST_F(InterfaceTypespecsOfARun, ATypeGivenByNameIsAssignedItsTypespec) {
  Run(kSBus);
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("top"), "SBbyte")),
            (std::vector<std::pair<std::string, int>>{{"T", vpiByteTypespec}}));
}

TEST_F(InterfaceTypespecsOfARun, AnOrderedValueAssignsANestedInterfacesParam) {
  Run("module top;\n"
      "  interface other #(parameter X = 0); endinterface\n"
      "  interface bus #(parameter W = 1, parameter D = 2); endinterface\n"
      "  typedef virtual bus #(4, 5) vb_t;\n"
      "  class C; typedef virtual bus #(6) cv_t; endclass\n"
      "endmodule\n");
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("top"), "vb_t")),
            (std::vector<std::pair<std::string, int>>{{"W", vpiConstant},
                                                      {"D", vpiConstant}}));
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(Assigned(Named(vpiTypedef, defn, "cv_t")),
            (std::vector<std::pair<std::string, int>>{{"W", vpiConstant}}));
}

TEST_F(InterfaceTypespecsOfARun, AnOrderedValueAssignsAUnitInterfacesParam) {
  Run("interface ubus #(parameter N = 2); endinterface\n"
      "package pk; typedef virtual ubus #(7) vp_t; endpackage\n"
      "typedef virtual ubus #(3) vu_t;\n"
      "module top; vu_t vu; ubus #(3) u(); endmodule\n");
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("pk"), "vp_t")),
            (std::vector<std::pair<std::string, int>>{{"N", vpiConstant}}));
  EXPECT_EQ(Assigned(vpi_handle(vpiTypespec, By("top.vu"))),
            (std::vector<std::pair<std::string, int>>{{"N", vpiConstant}}));
}

TEST_F(InterfaceTypespecsOfARun, AnOrderedValueAssignsANestedHoldersParam) {
  Run("module top;\n"
      "  interface bus #(parameter W = 1); endinterface\n"
      "  interface outer #(parameter X = 1); endinterface\n"
      "  module inner;\n"
      "    interface bus #(parameter K = 1); endinterface\n"
      "    typedef virtual bus #(3) t;\n"
      "    typedef virtual outer #(4) o;\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("top.i"), "t")),
            (std::vector<std::pair<std::string, int>>{{"K", vpiConstant}}));
  EXPECT_EQ(Assigned(Named(vpiTypedef, By("top.i"), "o")),
            (std::vector<std::pair<std::string, int>>{{"X", vpiConstant}}));
}

}  // namespace
}  // namespace delta
