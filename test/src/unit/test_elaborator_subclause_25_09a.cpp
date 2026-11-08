#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceElaboration, DeclarationOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, UnknownInterfaceType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  virtual not_an_interface vif;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unknown interface 'not_an_interface' in virtual interface", 2, "25.9"));
}

TEST(VirtualInterfaceElaboration, UnknownModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus;\n"
      "  logic a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module top;\n"
      "  virtual simple_bus.not_a_modport vif;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "modport 'not_a_modport' not found in interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceElaboration, AssignNull_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  initial vif = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, AssignMatchingVirtualInterface_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, AssignMatchingInterfaceInstance_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, AssignDifferentInterfaceType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  virtual bus_a va;\n"
      "  virtual bus_b vb;\n"
      "  initial va = vb;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface assignment between incompatible interface types", 6,
      "25.9"));
}

TEST(VirtualInterfaceElaboration, AssignInterfaceInstanceDifferentType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  virtual bus_a va;\n"
      "  initial va = u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface assignment from interface "
                            "instance of incompatible type",
                            6, "25.9"));
}

TEST(VirtualInterfaceElaboration, AssignInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  int i;\n"
      "  initial vif = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface can only be assigned from "
                            "another virtual interface, an interface instance, "
                            "or null",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ParameterValuesMatch_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  pbus #(16) u();\n"
      "  virtual pbus #(16) vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, ParameterValuesDiffer_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  pbus #(32) u();\n"
      "  virtual pbus #(16) vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface parameter values do not match "
                            "the interface instance",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ParameterValuesDifferAcrossVirtual_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  virtual pbus #(16) a;\n"
      "  virtual pbus #(32) b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface parameter values do not match",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ParameterOverrideFromParameterMatches_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top #(parameter P = 16);\n"
      "  virtual pbus #(P) a;\n"
      "  virtual pbus #(16) b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, ParameterOverrideFromParameterDiffers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top #(parameter P = 32);\n"
      "  virtual pbus #(P) a;\n"
      "  virtual pbus #(16) b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface parameter values do not match",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration,
     ParameterOverrideOnInstanceFromParameterMatches_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top #(parameter P = 16);\n"
      "  pbus #(P) u();\n"
      "  virtual pbus #(16) vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration,
     ParameterOverrideOnInstanceFromParameterDiffers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top #(parameter P = 32);\n"
      "  pbus #(P) u();\n"
      "  virtual pbus #(16) vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface parameter values do not match "
                            "the interface instance",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, NoModportToWithModport_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus.mp vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, NoModportVirtualToWithModport_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module top;\n"
      "  virtual simple_bus src;\n"
      "  virtual simple_bus.mp dst;\n"
      "  initial dst = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, WithModportToNoModport_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus;\n"
      "  logic a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module top;\n"
      "  virtual simple_bus.mp src;\n"
      "  virtual simple_bus dst;\n"
      "  initial dst = src;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface with modport cannot be assigned "
                            "to virtual interface without modport",
                            8, "25.9"));
}

TEST(VirtualInterfaceElaboration, EqualityWithVirtual_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b;\n"
      "  bit eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, EqualityWithInterfaceInstance_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus a;\n"
      "  bit eq;\n"
      "  initial eq = (a == u);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, InequalityWithNull_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a;\n"
      "  bit ne;\n"
      "  initial ne = (a != null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, EqualityDifferentType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  virtual bus_a va;\n"
      "  virtual bus_b vb;\n"
      "  bit eq;\n"
      "  initial eq = (va == vb);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "comparison between virtual interfaces of different types", 7, "25.9"));
}

TEST(VirtualInterfaceElaboration, EqualityWithIntLiteral_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a;\n"
      "  bit eq;\n"
      "  initial eq = (a == 5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface can only be compared with "
                            "another virtual interface, an interface instance, "
                            "or null",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, EqualityWithIntVariable_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a;\n"
      "  int i;\n"
      "  bit ne;\n"
      "  initial ne = (a != i);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface can only be compared with "
                            "another virtual interface, an interface instance, "
                            "or null",
                            6, "25.9"));
}

TEST(VirtualInterfaceElaboration,
     EqualityWithInterfaceInstanceDifferentType_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  virtual bus_a va;\n"
      "  bit eq;\n"
      "  initial eq = (va == u);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison between a virtual interface and an "
                            "interface instance of a different type",
                            7, "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperator_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, LessThanOperator_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b;\n"
      "  bit lt;\n"
      "  initial lt = (a < b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, BitwiseOrOperator_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b;\n"
      "  bit r;\n"
      "  initial r = |(a | b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, InputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(input virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot be used as a port type",
                            2, "25.9"));
}

TEST(VirtualInterfaceElaboration, OutputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(output virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot be used as a port type",
                            2, "25.9"));
}

TEST(VirtualInterfaceElaboration, InoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(inout virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot be used as a port type",
                            2, "25.9"));
}

TEST(VirtualInterfaceElaboration, InsideInterfaceItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface other_bus; endinterface\n"
      "interface host_bus;\n"
      "  virtual other_bus vif;\n"
      "endinterface\n"
      "module top;\n"
      "  host_bus u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be declared inside an interface", 3, "25.9"));
}

TEST(VirtualInterfaceElaboration, AsUntaggedUnionMember_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  typedef union { virtual simple_bus vif; int i; } u_t;\n"
      "  u_t u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used as a member of a union", 3, "25.9"));
}

TEST(VirtualInterfaceElaboration, AsPackedUnionMember_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  typedef union packed { virtual simple_bus vif; int i; } u_t;\n"
      "  u_t u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used as a member of a union", 3, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInContinuousAssignLhs_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  assign vif.a = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInContinuousAssignRhs_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  assign x = vif.a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInSensitivityList_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  always @(vif.a) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot appear in event expression", 4, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInProceduralStatement_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  initial begin\n"
      "    vif = u;\n"
      "    vif.a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, AsClassProperty_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "endclass\n"
      "module top;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, ClassPropertyInitializedViaNewArg_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "  function new(virtual simple_bus b); bus = b; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  C c;\n"
      "  initial c = new(u);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, DefparamOutsideInterface_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  pbus u();\n"
      "  defparam u.W = 16;\n"
      "  virtual pbus vif;\n"
      "  initial vif = u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface instance targeted by a defparam "
                            "declared outside the interface cannot be assigned "
                            "to a virtual interface",
                            6, "25.9"));
}

TEST(VirtualInterfaceElaboration, InterfaceWithExternalHierRefAsVi_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module other;\n"
      "  logic sig;\n"
      "endmodule\n"
      "interface ref_bus;\n"
      "  wire s = top.u.sig;\n"
      "endinterface\n"
      "module top;\n"
      "  other u();\n"
      "  virtual ref_bus vif;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface 'ref_bus' contains references to "
                            "objects outside its body and cannot be used as a "
                            "virtual interface",
                            9, "25.9"));
}

TEST(VirtualInterfaceElaboration, PassAsTaskArgument_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  task do_it(virtual simple_bus v); v.a = 1'b1; endtask\n"
      "  initial do_it(u);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, PassAsFunctionArgument_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  int x;\n"
      "  function int do_it(virtual simple_bus v); return 0; endfunction\n"
      "  initial x = do_it(u);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, PassAsMethodArgument_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "class C;\n"
      "  task do_it(virtual simple_bus v); v.a = 1'b1; endtask\n"
      "endclass\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new();\n"
      "    c.do_it(u);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, ParameterValuesMatchAcrossVirtual_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  virtual pbus #(16) a;\n"
      "  virtual pbus #(16) b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, DefparamOnSiblingInstanceAllowsAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface pbus #(parameter W = 8); endinterface\n"
      "module top;\n"
      "  pbus tainted();\n"
      "  defparam tainted.W = 16;\n"
      "  pbus clean();\n"
      "  virtual pbus vif;\n"
      "  initial vif = clean;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, InterfaceWithInterfacePortAsVi_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface outer_bus(interface ib); endinterface\n"
      "module top;\n"
      "  virtual outer_bus vif;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface 'outer_bus' contains references to "
                            "objects outside its body and cannot be used as a "
                            "virtual interface",
                            3, "25.9"));
}

TEST(VirtualInterfaceElaboration, PortTypeNames25_9) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(input virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot be used", 2, "25.9"));
}

TEST(VirtualInterfaceElaboration,
     ComponentInInferredAlwaysCombSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  always_comb x = vif.a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot appear in an inferred sensitivity list", 5,
      "25.9"));
}

TEST(VirtualInterfaceElaboration,
     ComponentInInferredAlwaysLatchSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x, en;\n"
      "  always_latch if (en) x <= vif.a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot appear in an inferred sensitivity list", 5,
      "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInStarSensitivityList_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  always @* x = vif.a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot appear in an inferred sensitivity list", 5,
      "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentWrittenInInferredProcedure_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  always_comb vif.a = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
