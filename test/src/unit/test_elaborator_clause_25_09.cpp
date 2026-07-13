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

// A virtual interface's parameter override may be any constant expression, not
// only a literal. When the override is a module parameter that resolves to the
// same value as the other interface's override, the two are the same type and
// the assignment is legal — exercising the override evaluated in module scope.
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

// The same rule with a parameter-valued override that resolves to a different
// value than the other side's literal override: the parameter values differ,
// so the two virtual interfaces are not the same type and the assignment is
// illegal. This only fires when the override is evaluated in the module's
// parameter scope rather than an empty one.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same parameter-match rule for the interface-instance source: when the
// instance's parameter override is itself a module parameter, it resolves to
// the same value as the virtual interface's override, so the assignment from
// instance to virtual interface is legal.
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

// An instance whose parameter override is a module parameter resolving to a
// value that differs from the virtual interface's override is not the same
// type, so the assignment is illegal. This only fires when the instance
// override is evaluated in the enclosing module's parameter scope.
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

// §25.9 restricts the operands of == / != on a virtual interface to another
// virtual interface of the same type, an interface instance, or null. Comparing
// a virtual interface against an integer literal is outside that whitelist.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// A virtual interface compared for equality against a variable of an
// incompatible data type (here an int) is likewise illegal.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// The equality whitelist admits an interface instance only when it is of the
// same interface type as the virtual interface. Comparing against an instance
// of a different interface is illegal.
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

// §25.9 allows a virtual interface variable to be passed as an argument to a
// function (the second of the three enumerated positions: tasks, functions,
// methods). An interface instance is passed through to the function's virtual
// interface formal and elaboration accepts it.
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

// The third enumerated position: a class method may take a virtual interface
// formal, and an interface instance is passed to it through an object handle.
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

// Two virtual interfaces of the same interface with identical parameter value
// overrides are the same type, so assignment between them is legal. Covers the
// matching-parameters path for a virtual-to-virtual assignment (the mismatch
// path is exercised by ParameterValuesDifferAcrossVirtual_Error).
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

// The defparam restriction is scoped to the specific interface instance the
// defparam targets. A defparam on a sibling instance must not block assigning
// a different, untargeted interface instance to a virtual interface.
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

// An interface whose ports reference other interfaces cannot be used as the
// type of a virtual interface.
TEST(VirtualInterfaceElaboration, InterfaceWithInterfacePortAsVi_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface outer_bus(interface ib); endinterface\n"
      "module top;\n"
      "  virtual outer_bus vif;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
