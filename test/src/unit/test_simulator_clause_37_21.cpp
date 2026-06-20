#include <gtest/gtest.h>

#include <vector>

#include "helpers_vpi_driver_load_iter.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
// and a procedural assignment statement - while skipping children that are
// neither.
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

  std::vector<VpiHandle> drivers =
      CollectVpiIteration(ctx, ctx.Iterate(vpiDriver, &union_var));
  ASSERT_EQ(drivers.size(), 2u);
  EXPECT_TRUE(VpiIterationContains(drivers, &whole_driver));
  EXPECT_TRUE(VpiIterationContains(drivers, &deep_driver));
}

}  // namespace
}  // namespace delta
