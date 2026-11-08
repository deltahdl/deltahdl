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

TEST(VariableDriversAndLoads, NonAggregateVariableDoesNotDescend) {
  VpiContext ctx;

  VpiObject direct_driver;
  direct_driver.type = vpiContAssign;

  VpiObject select_driver;
  select_driver.type = vpiForce;
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
  ASSERT_EQ(drivers.size(), 1u);
  EXPECT_TRUE(VpiIterationContains(drivers, &direct_driver));
  EXPECT_FALSE(VpiIterationContains(drivers, &select_driver));
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

}  // namespace
}  // namespace delta
