#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_vpi_driver_load_iter.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(VariableDriversAndLoads, DriverIterationReachesEveryDriverKind) {
  VpiContext ctx;

  VpiObject port;
  port.type = vpiPort;
  VpiObject force;
  force.type = vpiForce;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject unrelated;
  unrelated.type = vpiTypespec;

  VpiObject var;
  var.type = vpiLogicVar;
  var.children = {&port,        &unrelated,       &force,
                  &cont_assign, &cont_assign_bit, &assign_stmt};

  force.lhs = &var;
  cont_assign.lhs = &var;
  assign_stmt.lhs = &var;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &var));
  ASSERT_EQ(drivers.size(), 5u);
  EXPECT_TRUE(VpiIterationContains(drivers, &port));
  EXPECT_TRUE(VpiIterationContains(drivers, &force));
  EXPECT_TRUE(VpiIterationContains(drivers, &cont_assign));
  EXPECT_TRUE(VpiIterationContains(drivers, &cont_assign_bit));
  EXPECT_TRUE(VpiIterationContains(drivers, &assign_stmt));
  EXPECT_FALSE(VpiIterationContains(drivers, &unrelated));
}

TEST(VariableDriversAndLoads, LoadIterationExcludesPorts) {
  VpiContext ctx;

  VpiObject port;
  port.type = vpiPort;
  VpiObject force;
  force.type = vpiForce;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;

  VpiObject var;
  var.type = vpiLogicVar;
  var.children = {&port, &force, &cont_assign, &cont_assign_bit, &assign_stmt};

  force.rhs = &var;
  cont_assign.rhs = &var;
  assign_stmt.rhs = &var;
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &var));
  ASSERT_EQ(loads.size(), 4u);
  EXPECT_FALSE(VpiIterationContains(loads, &port));
  EXPECT_TRUE(VpiIterationContains(loads, &force));
  EXPECT_TRUE(VpiIterationContains(loads, &cont_assign));
  EXPECT_TRUE(VpiIterationContains(loads, &cont_assign_bit));
  EXPECT_TRUE(VpiIterationContains(loads, &assign_stmt));
}

TEST(VariableDriversAndLoads, AggregateDriverIncludesSelectsAndMembers) {
  VpiContext ctx;

  VpiObject whole_driver;
  whole_driver.type = vpiContAssign;

  VpiObject select_driver;
  select_driver.type = vpiForce;
  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.children = {&select_driver};

  VpiObject member_driver;
  member_driver.type = vpiAssignStmt;
  VpiObject member;
  member.type = vpiLogicVar;
  member.children = {&member_driver};

  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  struct_var.children = {&whole_driver, &part_select, &member};

  whole_driver.lhs = &struct_var;
  select_driver.lhs = &part_select;
  member_driver.lhs = &member;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &struct_var));
  ASSERT_EQ(drivers.size(), 3u);
  EXPECT_TRUE(VpiIterationContains(drivers, &whole_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &select_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &member_driver));
}

TEST(VariableDriversAndLoads, AggregateLoadIncludesNestedMembersNotPorts) {
  VpiContext ctx;

  VpiObject member_load;
  member_load.type = vpiForce;
  VpiObject member_port;
  member_port.type = vpiPort;
  VpiObject member;
  member.type = vpiLogicVar;
  member.children = {&member_load, &member_port};

  VpiObject whole_load;
  whole_load.type = vpiAssignStmt;

  VpiObject class_var;
  class_var.type = vpiClassVar;
  class_var.children = {&whole_load, &member};

  member_load.rhs = &member;
  whole_load.rhs = &class_var;
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &class_var));
  ASSERT_EQ(loads.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(loads, &whole_load));
  EXPECT_TRUE(VpiIterationContains(loads, &member_load));
  EXPECT_FALSE(VpiIterationContains(loads, &member_port));
}

TEST(VariableDriversAndLoads, DISABLED_AVectorTakesInTheDriverOfABitSelect) {
  VpiContext ctx;

  VpiObject direct_driver;
  direct_driver.type = vpiContAssign;

  VpiObject select_driver;
  select_driver.type = vpiContAssign;
  VpiObject bit_select;
  bit_select.type = vpiBitSelect;
  bit_select.children = {&select_driver};

  VpiObject var;
  var.type = vpiLogicVar;
  var.children = {&direct_driver, &bit_select};

  direct_driver.lhs = &var;
  select_driver.lhs = &bit_select;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &var));
  ASSERT_EQ(drivers.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(drivers, &direct_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &select_driver));
}

TEST(VariableDriversAndLoads, UnionDriverDescendsThroughNestedAggregateMember) {
  VpiContext ctx;

  VpiObject whole_driver;
  whole_driver.type = vpiContAssign;

  VpiObject deep_driver;
  deep_driver.type = vpiForce;
  VpiObject inner_member;
  inner_member.type = vpiLogicVar;
  inner_member.children = {&deep_driver};
  VpiObject struct_member;
  struct_member.type = vpiStructVar;
  struct_member.children = {&inner_member};

  VpiObject union_var;
  union_var.type = vpiUnionVar;
  union_var.children = {&whole_driver, &struct_member};

  whole_driver.lhs = &union_var;
  deep_driver.lhs = &inner_member;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &union_var));
  ASSERT_EQ(drivers.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(drivers, &whole_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &deep_driver));
}

TEST(VariableDriversAndLoads, ArrayDriverIncludesTheDriverOfAPortionOfIt) {
  VpiContext ctx;

  VpiObject whole_driver;
  whole_driver.type = vpiContAssign;

  VpiObject element_driver;
  element_driver.type = vpiForce;
  VpiObject select;
  select.type = vpiVarSelect;
  select.children = {&element_driver};

  VpiObject array;
  array.type = vpiArrayVar;
  array.children = {&whole_driver, &select};

  whole_driver.lhs = &array;
  element_driver.lhs = &select;
  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &array));
  ASSERT_EQ(drivers.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(drivers, &whole_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &element_driver));
}

TEST(VariableDriversAndLoads, PackedArrayLoadIncludesAPartSelectsLoad) {
  VpiContext ctx;

  VpiObject whole_load;
  whole_load.type = vpiAssignStmt;

  VpiObject portion_load;
  portion_load.type = vpiContAssign;
  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.children = {&portion_load};

  VpiObject vector;
  vector.type = vpiPackedArrayVar;
  vector.children = {&whole_load, &part_select};

  whole_load.rhs = &vector;
  portion_load.rhs = &part_select;
  std::vector<VpiHandle> loads =
      CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &vector));
  ASSERT_EQ(loads.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(loads, &whole_load));
  EXPECT_TRUE(VpiIterationContains(loads, &portion_load));
}

TEST(VariableDriversAndLoads, AnAssignmentDrivesItsTargetAndLoadsWhatItReads) {
  VpiContext ctx;

  VpiObject target;
  target.type = vpiLogicVar;
  VpiObject other;
  other.type = vpiLogicVar;
  VpiObject read;
  read.type = vpiLogicVar;
  VpiObject concat;
  concat.type = vpiOperation;
  concat.children = {&other, &target};
  VpiObject negation;
  negation.type = vpiOperation;
  negation.children = {&read};
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  cont_assign.lhs = &concat;
  cont_assign.rhs = &negation;
  target.children = {&cont_assign};
  read.children = {&cont_assign};

  EXPECT_TRUE(CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &read)).empty());
  EXPECT_TRUE(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &target)).empty());
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &target)).size(),
            1u);
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &read)).size(), 1u);
}

TEST(VariableDriversAndLoads, AnAssignmentWithNoTargetDrivesNothing) {
  VpiContext ctx;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject var;
  var.type = vpiLogicVar;
  var.children = {&assign_stmt};
  EXPECT_TRUE(CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &var)).empty());
}

TEST(VariableDriversAndLoads, ReadingASelectThroughASelectLoadsBothIndices) {
  VpiContext ctx;
  VpiObject i;
  i.type = vpiLogicVar;
  VpiObject j;
  j.type = vpiLogicVar;
  VpiObject array;
  array.type = vpiArrayVar;
  VpiObject inner;
  inner.type = vpiVarSelect;
  inner.parent = &array;
  inner.index_expr = &i;
  inner.children = {&i};
  VpiObject outer;
  outer.type = vpiVarSelect;
  outer.parent = &inner;
  outer.index_expr = &j;
  outer.children = {&j, &i};
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  cont_assign.rhs = &outer;
  i.children = {&cont_assign};
  j.children = {&cont_assign};
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &i)).size(), 1u);
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &j)).size(), 1u);
}

TEST(VariableDriversAndLoads, AnExpressionIsALoadPastASelectAndACall) {
  VpiContext ctx;
  VpiObject v;
  v.type = vpiLogicVar;
  VpiObject k;
  k.type = vpiLogicVar;
  VpiObject u;
  u.type = vpiLogicVar;
  VpiObject bit_select;
  bit_select.type = vpiBitSelect;
  bit_select.parent = &v;
  bit_select.index_expr = &k;
  VpiObject call;
  call.type = vpiFuncCall;
  call.arguments = {&k};
  VpiObject concat;
  concat.type = vpiOperation;
  concat.op_type = vpiConcatOp;
  concat.children = {&bit_select, &call, &u};
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  cont_assign.rhs = &concat;
  v.children = {&cont_assign};
  k.children = {&cont_assign};
  u.children = {&cont_assign};
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &u)).size(), 1u);
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &v)).size(), 1u);
  EXPECT_EQ(CollectVpiIteration(ctx, ctx.Iterate(vpiLoad, &k)).size(), 1u);
}

class VariableDriversOfARun : public VpiDesignRun {
 protected:
  static std::vector<int> KindsOf(int type, vpiHandle ref) {
    std::vector<int> kinds;
    vpiHandle it = ref == nullptr ? nullptr : vpi_iterate(type, ref);
    if (it == nullptr) return kinds;
    while (vpiHandle obj = vpi_scan(it)) kinds.push_back(vpi_get(vpiType, obj));
    std::ranges::sort(kinds);
    return kinds;
  }

  static constexpr const char* kDesign =
      "module m(input var logic i, output logic o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef struct packed { logic a; logic b; } s_t;\n"
      "  s_t s;\n"
      "  logic v, a, f, g, p, q;\n"
      "  assign v = a;\n"
      "  assign s.a = 1'b1;\n"
      "  m u(.i(p), .o(q));\n"
      "  initial begin\n"
      "    assign f = a;\n"
      "    force g = v | a;\n"
      "  end\n"
      "endmodule\n";
};

TEST_F(VariableDriversOfARun, AContinuousAssignmentDrivesOnlyItsTarget) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.v")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.v")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.a")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.a")),
            (std::vector<int>{vpiAssignStmt, vpiContAssign, vpiForce}));
}

TEST_F(VariableDriversOfARun, AnAssignStmtAndAForceDriveTheirTargets) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.f")), std::vector<int>{vpiAssignStmt});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.g")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, APortDrivesTheVariableItConnects) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.u.i")), std::vector<int>{vpiPort});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.q")), std::vector<int>{vpiPort});
}

TEST_F(VariableDriversOfARun, AnAssignmentToAMemberDrivesTheStructure) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.s")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AForceReadingASelectThroughASelectLoadsTheArray) {
  Run("module top;\n"
      "  logic m [0:1][0:1];\n"
      "  logic o, i, j;\n"
      "  initial force o = m[i][j];\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.m")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, AnArrayTakesInNothingOfItsSelectsIndices) {
  Run("module top;\n"
      "  logic m [0:1];\n"
      "  logic i, o, o2;\n"
      "  assign o = m[i];\n"
      "  assign o2 = i;\n"
      "  initial force i = 1'b0;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.m")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.m")), std::vector<int>{});
}

TEST_F(VariableDriversOfARun, AnAssignmentLoadsWhatACallsArgumentsRead) {
  Run("module top;\n"
      "  function automatic logic f(logic a); return a; endfunction\n"
      "  logic t, u, o, p;\n"
      "  assign o = f(t);\n"
      "  assign p = $unsigned(u);\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.t")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.u")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AForceLoadsWhatItsIndicesAndArgumentsRead) {
  Run("module top;\n"
      "  function automatic logic f(logic a); return a; endfunction\n"
      "  logic [3:0] v;\n"
      "  logic m [0:1][0:1];\n"
      "  logic [1:0] o2;\n"
      "  logic o1, o3, o4, i, b, k, l, t;\n"
      "  initial begin\n"
      "    force o1 = v[i];\n"
      "    force o2 = v[b +: 2];\n"
      "    force o3 = m[k][l];\n"
      "    force o4 = f(t);\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.i", "top.b", "top.k", "top.l", "top.t"}) {
    EXPECT_EQ(KindsOf(vpiLoad, By(name)), std::vector<int>{vpiForce}) << name;
  }
}

TEST_F(VariableDriversOfARun, APortDrivesOnlyTheSideItsDirectionWrites) {
  Run(kDesign);
  ASSERT_NE(By("top.p"), nullptr);
  ASSERT_NE(By("top.u.o"), nullptr);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.p")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.u.o")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, APortIsNeverALoad) {
  Run(kDesign);
  ASSERT_NE(By("top.p"), nullptr);
  ASSERT_NE(By("top.u.o"), nullptr);
  EXPECT_EQ(KindsOf(vpiLoad, By("top.p")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.u.o")), std::vector<int>{});
}

TEST_F(VariableDriversOfARun, ARefPortDrivesNothing) {
  Run("module r(ref logic x);\n"
      "endmodule\n"
      "module top;\n"
      "  logic rv;\n"
      "  r ur(.x(rv));\n"
      "endmodule\n");
  ASSERT_NE(By("top.rv"), nullptr);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.rv")), std::vector<int>{});
}

TEST_F(VariableDriversOfARun, AConcatenationTargetDrivesEachOperand) {
  Run("module top;\n"
      "  logic x, y, f1, f2, g1, g2;\n"
      "  assign {x, y} = 2'b10;\n"
      "  initial begin\n"
      "    assign {f1, f2} = 2'b01;\n"
      "    force {g1, g2} = 2'b11;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.x")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.y")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.f1")), std::vector<int>{vpiAssignStmt});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.f2")), std::vector<int>{vpiAssignStmt});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.g1")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.g2")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, AProceduralAssignmentDrivesAndLoadsNothing) {
  Run("module top;\n"
      "  logic c, v, o, o2;\n"
      "  always @* o = v;\n"
      "  always @(posedge c) o2 <= v;\n"
      "endmodule\n");
  ASSERT_NE(By("top.v"), nullptr);
  ASSERT_NE(By("top.o"), nullptr);
  ASSERT_NE(By("top.o2"), nullptr);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.o")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.o2")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.v")), std::vector<int>{});
}

TEST_F(VariableDriversOfARun, EveryVariableKindIsDrivenByEachAssignmentKind) {
  Run("module top;\n"
      "  typedef enum logic [1:0] { A, B } e_t;\n"
      "  int ic, if_, ia;\n"
      "  bit bc, bf, ba;\n"
      "  real rc, rf, ra;\n"
      "  e_t ec, ef, ea;\n"
      "  string sc, sf, sa;\n"
      "  assign ic = 1;\n"
      "  assign bc = 1'b1;\n"
      "  assign rc = 1.5;\n"
      "  assign ec = B;\n"
      "  assign sc = \"x\";\n"
      "  initial begin\n"
      "    force if_ = 2;\n"
      "    force bf = 1'b0;\n"
      "    force rf = 2.5;\n"
      "    force ef = A;\n"
      "    force sf = \"y\";\n"
      "    assign ia = 3;\n"
      "    assign ba = 1'b1;\n"
      "    assign ra = 3.5;\n"
      "    assign ea = B;\n"
      "    assign sa = \"z\";\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.ic", "top.bc", "top.rc", "top.ec", "top.sc"}) {
    EXPECT_EQ(KindsOf(vpiDriver, By(name)), std::vector<int>{vpiContAssign})
        << name;
  }
  for (const char* name : {"top.if_", "top.bf", "top.rf", "top.ef", "top.sf"}) {
    EXPECT_EQ(KindsOf(vpiDriver, By(name)), std::vector<int>{vpiForce}) << name;
  }
  for (const char* name : {"top.ia", "top.ba", "top.ra", "top.ea", "top.sa"}) {
    EXPECT_EQ(KindsOf(vpiDriver, By(name)), std::vector<int>{vpiAssignStmt})
        << name;
  }
}

TEST_F(VariableDriversOfARun, AVariableOfEveryScopeKindHasItsDrivers) {
  Run("package pkg;\n"
      "  logic pv;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic x;\n"
      "  assign x = 1'b1;\n"
      "endinterface\n"
      "program prg;\n"
      "  logic y;\n"
      "  initial force y = 1'b0;\n"
      "endprogram\n"
      "module top;\n"
      "  ifc i0();\n"
      "  prg p0();\n"
      "  if (1) begin : g\n"
      "    logic z;\n"
      "    assign z = 1'b1;\n"
      "  end\n"
      "  initial force pkg::pv = 1'b1;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.i0.x")),
            std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.p0.y")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.g.z")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("pkg::pv")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, AForceOrAssignInASubroutineDrivesItsTarget) {
  Run("module top;\n"
      "  logic tf, ta, ff, fa;\n"
      "  task t;\n"
      "    force tf = 1'b1;\n"
      "    assign ta = 1'b0;\n"
      "  endtask\n"
      "  function void fn;\n"
      "    force ff = 1'b1;\n"
      "    assign fa = 1'b0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    t();\n"
      "    fn();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.tf")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.ta")), std::vector<int>{vpiAssignStmt});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.ff")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.fa")), std::vector<int>{vpiAssignStmt});
}

TEST_F(VariableDriversOfARun, AnAssignStmtLoadsWhatItsIndicesAndArgumentsRead) {
  Run("module top;\n"
      "  function automatic logic f(logic a); return a; endfunction\n"
      "  logic [3:0] v;\n"
      "  logic m [0:1][0:1];\n"
      "  logic [1:0] o2;\n"
      "  logic o0, o1, o3, o4, i, b, k, l, t;\n"
      "  initial begin\n"
      "    assign o0 = t;\n"
      "    assign o1 = v[i];\n"
      "    assign o2 = v[b +: 2];\n"
      "    assign o3 = m[k][l];\n"
      "    assign o4 = f(t);\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.i", "top.b", "top.k", "top.l"}) {
    EXPECT_EQ(KindsOf(vpiLoad, By(name)), std::vector<int>{vpiAssignStmt})
        << name;
  }
  EXPECT_EQ(KindsOf(vpiLoad, By("top.t")),
            (std::vector<int>{vpiAssignStmt, vpiAssignStmt}));
}

TEST_F(VariableDriversOfARun, AVectorContinuousAssignmentIsOneDriverAndLoad) {
  Run("module top;\n"
      "  logic [3:0] v, a;\n"
      "  assign v = a;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.v")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.a")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AStructureTakesInItsSelectsAndNestedMembers) {
  Run("module top;\n"
      "  typedef struct packed {\n"
      "    struct packed { logic x; logic y; } n;\n"
      "    logic a;\n"
      "  } p_t;\n"
      "  typedef struct {\n"
      "    logic a;\n"
      "    struct { logic x; logic y; } n;\n"
      "  } u_t;\n"
      "  p_t pw, ps, pn;\n"
      "  u_t uw, um, un;\n"
      "  logic c;\n"
      "  assign pw = 3'b101;\n"
      "  assign ps[0] = c;\n"
      "  assign ps[2:1] = 2'b10;\n"
      "  assign pn.n.x = c;\n"
      "  assign uw = '{1'b0, '{1'b1, 1'b0}};\n"
      "  assign um.a = c;\n"
      "  assign un.n.x = c;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.pw")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.ps")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiDriver, By("top.pn")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.uw")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.um")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.un")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AStructureLoadIncludesItsSelectsAndMembers) {
  Run("module top;\n"
      "  typedef struct packed { logic a; logic b; } s_t;\n"
      "  typedef struct { logic a; struct { logic x; } n; } u_t;\n"
      "  s_t s;\n"
      "  u_t u;\n"
      "  s_t o1;\n"
      "  logic o2, o3, o4, o5;\n"
      "  assign o1 = s;\n"
      "  assign o2 = s[0];\n"
      "  assign o3 = s.a;\n"
      "  assign o4 = u.a;\n"
      "  assign o5 = u.n.x;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.s")),
            (std::vector<int>{vpiContAssign, vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiLoad, By("top.u")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
}

TEST_F(VariableDriversOfARun, AUnionTakesInItsSelectsAndMembers) {
  Run("module top;\n"
      "  typedef union packed { logic [3:0] w; logic [3:0] z; } p_t;\n"
      "  typedef union { logic [3:0] w; int k; } u_t;\n"
      "  p_t pw, pm, ps;\n"
      "  u_t um;\n"
      "  logic c;\n"
      "  assign pw = 4'b1010;\n"
      "  assign pm.z = 4'b0011;\n"
      "  assign ps[0] = c;\n"
      "  assign ps[3:2] = 2'b01;\n"
      "  assign um.w = 4'b0110;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.pw")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.pm")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.ps")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiDriver, By("top.um")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AUnionLoadIncludesItsSelectsAndMembers) {
  Run("module top;\n"
      "  typedef union packed { logic [3:0] w; logic [3:0] z; } p_t;\n"
      "  typedef union { logic [3:0] w; int k; } u_t;\n"
      "  p_t p;\n"
      "  u_t u;\n"
      "  p_t o1;\n"
      "  logic o2;\n"
      "  logic [3:0] o3, o4;\n"
      "  assign o1 = p;\n"
      "  assign o2 = p[1];\n"
      "  assign o3 = p.z;\n"
      "  assign o4 = u.w;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.p")),
            (std::vector<int>{vpiContAssign, vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiLoad, By("top.u")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun, AClassVariableIsDrivenAndLoadedWhole) {
  Run("module top;\n"
      "  class C;\n"
      "    logic x;\n"
      "  endclass\n"
      "  C c, h;\n"
      "  initial begin\n"
      "    force c = null;\n"
      "    force h = c;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.c")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.c")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, DISABLED_AClassVariableLoadIncludesAMembersLoad) {
  Run("module top;\n"
      "  class C;\n"
      "    logic x;\n"
      "  endclass\n"
      "  C c;\n"
      "  logic o;\n"
      "  initial force o = c.x;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.c")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, AnUnpackedArrayTakesInItsElementsAndWhole) {
  Run("module top;\n"
      "  logic m [0:1];\n"
      "  logic o [0:1];\n"
      "  logic d [0:1][0:1];\n"
      "  logic c;\n"
      "  assign m[0] = c;\n"
      "  assign o = m;\n"
      "  assign d[0][1] = c;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.m")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.m")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.d")), std::vector<int>{vpiContAssign});
}

TEST_F(VariableDriversOfARun,
       DISABLED_ADynamicArrayLoadIncludesAnElementsLoad) {
  Run("module top;\n"
      "  logic d [];\n"
      "  logic q [$];\n"
      "  logic a [int];\n"
      "  logic o1, o2, o3;\n"
      "  initial begin\n"
      "    force o1 = d[1];\n"
      "    force o2 = q[0];\n"
      "    force o3 = a[5];\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.d")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.q")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.a")), std::vector<int>{vpiForce});
}

TEST_F(VariableDriversOfARun, AVectorTakesInItsSelects) {
  Run("module top;\n"
      "  logic [7:0] v, w;\n"
      "  logic [1:0][3:0] p, r;\n"
      "  logic a, o1;\n"
      "  logic [3:0] b, o2, o3, o4;\n"
      "  assign v[3] = a;\n"
      "  assign v[7:4] = b;\n"
      "  assign p[0] = b;\n"
      "  assign o1 = w[3];\n"
      "  assign o2 = w[7:4];\n"
      "  assign o3 = r[1];\n"
      "  assign o4 = r[0][3:0];\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.v")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiDriver, By("top.p")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.w")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
  EXPECT_EQ(KindsOf(vpiLoad, By("top.r")),
            (std::vector<int>{vpiContAssign, vpiContAssign}));
}

TEST_F(VariableDriversOfARun,
       DISABLED_AnArrayOfStructuresTakesInItsElementsMembers) {
  Run("module top;\n"
      "  typedef struct packed { logic f; logic g; } e_t;\n"
      "  e_t s [0:1];\n"
      "  logic a, o;\n"
      "  assign s[0].f = a;\n"
      "  assign o = s[1].g;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiDriver, By("top.s")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.s")), std::vector<int>{vpiContAssign});
}

}  // namespace
}  // namespace delta
