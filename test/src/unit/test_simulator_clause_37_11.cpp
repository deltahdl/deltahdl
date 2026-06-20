#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.11 Instance arrays: the VPI instance-array object model. These tests
// observe the production helpers in vpi.cpp (and the VpiContext::Handle path
// they feed) that apply the clause's two numbered "Details".
//
// The diagram's structural one-to-many edges (instance array -> instance,
// module array -> module, program array -> param assign, interface array ->
// instance, primitive array -> primitive, the access-by-index and name/size
// properties) are walked by the generic object-model machinery and the
// vpi_handle_by_index()/vpi_handle_by_multi_index() routines owned by §38.19
// and §38.20, so they carry no production rule of their own here. The two
// details that do - the connection-list expr (detail 1) and the range
// iteration/bounds (detail 2) - are exercised below, resting on the
// instance-array/primitive- array grouping the diagram defines.

// The instance-array grouping the diagram draws: module, interface, and program
// arrays plus the instance-array supertype, and a primitive array (itself a
// kind of instance array). A non-array object kind is not in the group.
TEST(InstanceArrayModel, InstanceArrayTypeClassification) {
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiInstanceArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiModuleArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiInterfaceArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiProgramArray));
  // A primitive array is itself a kind of instance array.
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiPrimitiveArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiGateArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiSwitchArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiUdpArray));
  // A single module instance is not an array.
  EXPECT_FALSE(VpiIsInstanceArrayType(vpiModule));
}

// The primitive-array subgroup: a primitive array and the gate, switch, and udp
// array forms drawn beneath it. A module array is an instance array but not a
// primitive array.
TEST(InstanceArrayModel, PrimitiveArrayTypeClassification) {
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiPrimitiveArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiGateArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiSwitchArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiUdpArray));
  EXPECT_FALSE(VpiIsPrimitiveArrayType(vpiModuleArray));
  EXPECT_FALSE(VpiIsPrimitiveArrayType(vpiModule));
}

// D1: the expr reached from an instance array is the operation object listing
// the array's actual connections - the array's operation child.
TEST(InstanceArrayModel, ConnectionsAreTheOperationChild) {
  VpiObject array;
  array.type = vpiModuleArray;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  array.children.push_back(&op);

  EXPECT_EQ(VpiInstanceArrayConnections(&array), &op);
  // A null handle, and a handle that is not an instance array, reach none.
  EXPECT_EQ(VpiInstanceArrayConnections(nullptr), nullptr);
  VpiObject single_module;
  single_module.type = vpiModule;
  single_module.children.push_back(&op);
  EXPECT_EQ(VpiInstanceArrayConnections(&single_module), nullptr);
  // An instance array with no operation child reaches none.
  VpiObject empty_array;
  empty_array.type = vpiModuleArray;
  EXPECT_EQ(VpiInstanceArrayConnections(&empty_array), nullptr);
}

// D1 (edge): the connection list is located by object kind, not by position, so
// it is still reached when a non-operation child precedes it among the array's
// children.
TEST(InstanceArrayModel, ConnectionsSkipNonOperationChildren) {
  VpiObject array;
  array.type = vpiInterfaceArray;
  VpiObject leading;  // a non-operation child encountered first
  leading.type = vpiRange;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  array.children.push_back(&leading);
  array.children.push_back(&op);

  EXPECT_EQ(VpiInstanceArrayConnections(&array), &op);
}

// D1: that expr shall be a simple expression object of type vpiOperation whose
// vpiOpType is vpiListOp.
TEST(InstanceArrayModel, ConnectionExprIsListOperation) {
  VpiObject list_op;
  list_op.type = vpiOperation;
  list_op.op_type = vpiListOp;
  EXPECT_TRUE(VpiInstanceArrayConnectionsIsListOp(&list_op));

  // A different operation type does not satisfy the rule, and neither does a
  // non-operation object or a null handle.
  VpiObject other_op;
  other_op.type = vpiOperation;
  other_op.op_type = vpiConcatOp;
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(&other_op));
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(&constant));
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(nullptr));
}

// D1: traversing vpiExpr through the public handle path returns the list
// operation, and the object it returns satisfies the type/op-type rule.
TEST(InstanceArrayPublic, HandleExprReturnsListOperation) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject array;
  array.type = vpiModuleArray;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  array.children.push_back(&op);

  VpiHandle expr = ctx.Handle(vpiExpr, &array);
  ASSERT_EQ(expr, &op);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiOperation);
  EXPECT_EQ(ctx.Get(vpiOpType, expr), vpiListOp);
  EXPECT_TRUE(VpiInstanceArrayConnectionsIsListOp(expr));

  // A single instance (not an array) does not divert vpiExpr to a list op.
  VpiObject single;
  single.type = vpiModule;
  single.children.push_back(&op);
  EXPECT_EQ(ctx.Handle(vpiExpr, &single), nullptr);

  SetGlobalVpiContext(nullptr);
}

// D1 (edge): the detail applies to the whole instance-array group, so a
// primitive array (a gate array here) also diverts vpiExpr to its list
// operation through the public handle path, not only a module array.
TEST(InstanceArrayPublic, HandleExprDivertsForPrimitiveArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject gate_array;
  gate_array.type = vpiGateArray;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  gate_array.children.push_back(&op);

  VpiHandle expr = ctx.Handle(vpiExpr, &gate_array);
  ASSERT_EQ(expr, &op);
  EXPECT_TRUE(VpiInstanceArrayConnectionsIsListOp(expr));

  SetGlobalVpiContext(nullptr);
}

// D2: vpi_iterate(vpiRange, instance_array) returns one range per declared
// dimension, beginning with the leftmost range and iterating through the
// rightmost. A dynamic/queue/associative dimension contributes an empty range.
TEST(InstanceArrayModel, RangesRunLeftmostToRightmost) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[0].size = 4;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;
  dims[1].size = 2;

  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  // Leftmost dimension first.
  EXPECT_EQ(ranges[0].left_expr, &l0);
  EXPECT_EQ(ranges[0].right_expr, &r0);
  EXPECT_EQ(ranges[1].left_expr, &l1);
  EXPECT_EQ(ranges[1].right_expr, &r1);

  // No dimensions -> no ranges.
  EXPECT_TRUE(VpiInstanceArrayRanges({}).empty());
}

// D2: vpiLeftRange/vpiRightRange return the bounds of the leftmost dimension of
// a (possibly multidimensional) array.
TEST(InstanceArrayModel, LeftRightRangeReportLeftmostDimension) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;

  EXPECT_EQ(VpiInstanceArrayLeftRange(dims), &l0);
  EXPECT_EQ(VpiInstanceArrayRightRange(dims), &r0);

  // An array with no dimensions reports NULL for both relations.
  EXPECT_EQ(VpiInstanceArrayLeftRange({}), nullptr);
  EXPECT_EQ(VpiInstanceArrayRightRange({}), nullptr);
}

// D2: a leftmost dimension that is an empty range (dynamic/queue/associative)
// makes both bound relations report NULL, deferring to §37.22's empty-range
// rule.
TEST(InstanceArrayModel, EmptyLeftmostRangeReportsNullBounds) {
  VpiObject l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kQueue;  // empty range
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;

  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_TRUE(ranges[0].empty);
  EXPECT_EQ(VpiInstanceArrayLeftRange(dims), nullptr);
  EXPECT_EQ(VpiInstanceArrayRightRange(dims), nullptr);
}

}  // namespace
}  // namespace delta
