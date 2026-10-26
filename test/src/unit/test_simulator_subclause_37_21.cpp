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

// §37.21 Variable drivers and loads: the vpiDriver and vpiLoad edges relate a
// variable to the objects that drive it and the objects that read it. A driver
// is a port, a force, a continuous assignment (whole or single bit), or a
// procedural assignment statement; a load is the same set without a port, since
// a port only drives. The figure's structural edge and §37.21's two details are
// exercised here through the public iterate/scan API:
//   figure   - vpiDriver/vpiLoad reach the driver/load object kinds, and a port
//              counts only as a driver;
//   detail 1 - for a structure, union, or class variable the relation also
//              includes the drivers/loads of any bit/part-select of the
//              variable and of any member nested inside it;
//   detail 2 - the variable-array recommendation is a "should", carrying no
//              enforced behaviour, so it is not exercised here.

// Figure: vpiDriver on a variable reaches every kind of driver object - a port,
// a force, a continuous assignment, a single bit of a continuous assignment,
// and a procedural assignment statement, each one whose target is the
// variable - while skipping children that are neither.
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

// Figure: vpiLoad reaches the load object kinds but never a port. A port drives
// a variable only, so even though the variable carries one it is left out of
// the load iteration while the force, continuous assignment, and assignment
// statement are reported.
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

// Detail 1: a structure variable's vpiDriver iteration includes the driver of
// the whole variable, the driver of a bit/part-select of it, and the driver of
// a member nested inside it - all three categories the detail enumerates.
TEST(VariableDriversAndLoads, AggregateDriverIncludesSelectsAndMembers) {
  VpiContext ctx;

  // Whole-variable driver.
  VpiObject whole_driver;
  whole_driver.type = vpiContAssign;

  // Driver reached through a part-select of the variable.
  VpiObject select_driver;
  select_driver.type = vpiForce;
  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.children = {&select_driver};

  // Driver reached through a nested member of the variable.
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

// Detail 1 (load side, class variable): the load of a member nested inside a
// class variable is included, while the figure's port exclusion still holds
// even for a port attached to that nested member.
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

// Detail 1 is scoped to structure/union/class variables: a plain
// (non-aggregate) variable contributes only its own direct drivers. A driver
// sitting under a select child of such a variable is not reached, so the
// descent behaviour does not leak into ordinary variables.
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

// Detail 1 (union variable, nested aggregate member): the rule names structure,
// union, and class variables alike. A union variable's vpiDriver iteration
// therefore descends too, and because a member may itself be an aggregate the
// descent recurses: the driver of a logic var nested inside a structure member
// of the union is reached, alongside the whole-union driver.
TEST(VariableDriversAndLoads, UnionDriverDescendsThroughNestedAggregateMember) {
  VpiContext ctx;

  // Whole-variable driver on the union.
  VpiObject whole_driver;
  whole_driver.type = vpiContAssign;

  // A structure member of the union, itself holding a member with a driver, so
  // reaching it requires the descent to recurse past the first member level.
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

// Detail 2: a variable array's vpiDrivers and vpiLoads take in the drivers and
// loads of the whole array or vector and of every part of it a handle can be
// had to. A var select is that portion (§37.19), so an array variable's
// vpiDriver iteration reaches the driver of the element a select names
// alongside the driver of the whole array. Only the detail 1 arm was applied,
// so an array was walked as an ordinary variable and reported the whole-array
// driver alone.
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

// Detail 2 on the load side, and on the vector the detail names beside the
// array: a packed array variable is that vector, and the load of a part-select
// of it is a load of a portion a handle can be obtained for.
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

// Figure: an assignment hung on both what it writes and what it reads drives
// only the first and loads only the second, the side naming a variable
// deciding which it is, through a concatenation it writes and an operation it
// reads alike (#7021).
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

// Figure: an assignment drives a variable through the target it writes, so
// one hung on the variable with no target drives nothing.
TEST(VariableDriversAndLoads, AnAssignmentWithNoTargetDrivesNothing) {
  VpiContext ctx;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject var;
  var.type = vpiLogicVar;
  var.children = {&assign_stmt};
  EXPECT_TRUE(CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &var)).empty());
}

// §37.19 with §37.17 detail 5: a select through another, m[i][j], holds its
// own index j as its index and reaches the outer index i only among its
// children, and an assignment reading it is a load of both indices.
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

// Figure: the expression {v[k], f(k), u} is a load of u past a bit select and
// a call reading other variables, of v through the select and of k through
// the select's index.
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

// §37.21 against a design read and run whole.
class VariableDriversOfARun : public VpiDesignRun {
 protected:
  // The kinds of the objects `ref` reaches through `type`, in ascending
  // order, since the iteration fixes none.
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

// Figure: `assign v = a` drives v and loads a, and is no load of v and no
// driver of a (#7021); `force g = v | a` loads both through its operation.
TEST_F(VariableDriversOfARun, AContinuousAssignmentDrivesOnlyItsTarget) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.v")), std::vector<int>{vpiContAssign});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.v")), std::vector<int>{vpiForce});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.a")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiLoad, By("top.a")),
            (std::vector<int>{vpiAssignStmt, vpiContAssign, vpiForce}));
}

// Figure: a procedural assign and a force drive the variables they write
// (#7022).
TEST_F(VariableDriversOfARun, AnAssignStmtAndAForceDriveTheirTargets) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.f")), std::vector<int>{vpiAssignStmt});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.g")), std::vector<int>{vpiForce});
}

// Figure: an input port drives the variable inside its instance, and an
// output port the variable its connection names (#7023). The input is
// declared `var`, since an input of a data type alone is a net (§23.2.2.3).
TEST_F(VariableDriversOfARun, APortDrivesTheVariableItConnects) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.u.i")), std::vector<int>{vpiPort});
  EXPECT_EQ(KindsOf(vpiDriver, By("top.q")), std::vector<int>{vpiPort});
}

// Detail 1: `assign s.a = 1'b1` drives the structure variable s (#7024).
TEST_F(VariableDriversOfARun, AnAssignmentToAMemberDrivesTheStructure) {
  Run(kDesign);
  EXPECT_EQ(KindsOf(vpiDriver, By("top.s")), std::vector<int>{vpiContAssign});
}

// Detail 2: a force reading a select through another select, m[i][j], is a
// load of the array both selects are taken from, reached from the outer select
// through the inner one.
TEST_F(VariableDriversOfARun, AForceReadingASelectThroughASelectLoadsTheArray) {
  Run("module top;\n"
      "  logic m [0:1][0:1];\n"
      "  logic o, i, j;\n"
      "  initial force o = m[i][j];\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiLoad, By("top.m")), std::vector<int>{vpiForce});
}

}  // namespace
}  // namespace delta
