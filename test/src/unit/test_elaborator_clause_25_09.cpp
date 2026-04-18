#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, InputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(input virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, OutputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(output virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, InoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module m(inout virtual simple_bus vif);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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

}  // namespace
