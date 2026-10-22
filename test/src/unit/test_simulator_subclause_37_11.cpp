#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_vpi_two_fixed_unpacked_dims.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  std::vector<VpiArrayDimension> dims =
      MakeTwoFixedUnpackedDims({&l0, &r0, 4}, {&l1, &r1, 2});

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

// -----------------------------------------------------------------------------
// The class edges. §37.11 draws `instance array` in bold italic inside a dotted
// enclosure holding the module, interface and program arrays, with `primitive
// array` -- itself an enclosure over the gate, switch and udp arrays -- nested
// among them. §37.4.1 makes each a grouping rather than an object, so
// vpiInstanceArray and vpiPrimitiveArray are the two groups' names; matching
// either against an object's own type, which is what the generic traversal
// does, reached no array a design instantiates.
// -----------------------------------------------------------------------------

// §37.5 (figure, module <==> instance array): a module's instance arrays are
// what the edge drawn to the class reaches. A primitive array is drawn inside
// the same enclosure, so it comes back too; a module that is not an array does
// not.
TEST(InstanceArrayPublic, AModuleIteratesTheInstanceArraysItHolds) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject module_array;
  module_array.type = vpiModuleArray;
  VpiObject single;
  single.type = vpiModule;
  VpiObject gate_array;
  gate_array.type = vpiGateArray;

  VpiObject mod;
  mod.type = vpiModule;
  mod.children = {&module_array, &single, &gate_array};

  vpiHandle it = vpi_iterate(vpiInstanceArray, VpiHandleOf(&mod));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &module_array);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &gate_array);
  EXPECT_EQ(vpi_scan(it), nullptr);

  SetGlobalVpiContext(nullptr);
}

// §37.11 (figure, primitive array): the nested enclosure names a group of its
// own, so its edge reaches the gate, switch and udp arrays and not the module
// array drawn beside them.
TEST(InstanceArrayPublic, ThePrimitiveArrayEdgeReachesOnlyPrimitiveArrays) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject module_array;
  module_array.type = vpiModuleArray;
  VpiObject switch_array;
  switch_array.type = vpiSwitchArray;
  VpiObject udp_array;
  udp_array.type = vpiUdpArray;

  VpiObject mod;
  mod.type = vpiModule;
  mod.children = {&module_array, &switch_array, &udp_array};

  vpiHandle it = vpi_iterate(vpiPrimitiveArray, VpiHandleOf(&mod));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &switch_array);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &udp_array);
  EXPECT_EQ(vpi_scan(it), nullptr);

  SetGlobalVpiContext(nullptr);
}

// §37.11: a module holding no array of either kind reaches none, which §38.23
// reports as no iterator.
TEST(InstanceArrayPublic, AModuleWithNoArraysIteratesToNone) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject single;
  single.type = vpiModule;

  VpiObject mod;
  mod.type = vpiModule;
  mod.children = {&single};

  EXPECT_EQ(vpi_iterate(vpiInstanceArray, VpiHandleOf(&mod)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiPrimitiveArray, VpiHandleOf(&mod)), nullptr);

  SetGlobalVpiContext(nullptr);
}

// The instance arrays of a run: those a design declares, built from the
// elaborated design rather than by hand (#4932, #5070).
class InstanceArraysOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // The first terminal of `prim`.
  static vpiHandle FirstTerm(vpiHandle prim) {
    vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

// A module instance array is an object over its elements, sized and ranged as
// declared and reaching each by its index, which each element reaches too.
TEST_F(InstanceArraysOfARun, AModuleArrayIsAnObjectOverItsElements) {
  Run("module sub; endmodule\n"
      "module top; sub arr[2:4] (); endmodule\n");
  vpiHandle arr = By("top.arr");
  ASSERT_NE(arr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, arr), vpiModuleArray);
  EXPECT_EQ(vpi_get(vpiSize, arr), 3);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, arr)), 2);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, arr)), 4);
  EXPECT_EQ(KindsOf(vpiModule, arr).size(), 3U);
  vpiHandle element = By("top.arr[3]");
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(arr, 3)), VpiObjectOf(element));
  EXPECT_EQ(vpi_get(vpiArrayMember, element), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, element)), 3);
}

// An interface instance array is an interface array.
TEST_F(InstanceArraysOfARun, AnInterfaceArrayIsAnInterfaceArray) {
  Run("interface ifc; endinterface\n"
      "module top; ifc ifs[0:1] (); endmodule\n");
  vpiHandle ifs = By("top.ifs");
  ASSERT_NE(ifs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ifs), vpiInterfaceArray);
  EXPECT_EQ(vpi_get(vpiSize, ifs), 2);
}

// A gate instance array is a gate array over a gate per element, each reaching
// its index, and an element's terminal on a vector as wide as the array is
// that vector's bit the element takes, the rightmost element the least
// significant (§28.3.6).
TEST_F(InstanceArraysOfARun, AGateArrayIsAnObjectOverItsGates) {
  Run("module top; wire [3:0] y; logic [3:0] a, b;\n"
      "  and g[3:0] (y, a, b);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiGateArray, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle array = vpi_scan(it);
  ASSERT_NE(array, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, array), "g");
  EXPECT_EQ(vpi_get(vpiSize, array), 4);
  vpiHandle g2 = vpi_handle_by_index(array, 2);
  ASSERT_NE(g2, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g2), vpiGate);
  EXPECT_EQ(vpi_get(vpiArrayMember, g2), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, g2)), 2);
  vpiHandle out = FirstTerm(g2);
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, out)),
            VpiObjectOf(vpi_handle_by_index(By("top.y"), 2)));
}

// The terminals of `prim`, in the order written.
std::vector<vpiHandle> TermsOf(vpiHandle prim) {
  std::vector<vpiHandle> terms;
  vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
  while (vpiHandle term = it == nullptr ? nullptr : vpi_scan(it)) {
    terms.push_back(term);
  }
  return terms;
}

// The one primitive array `scope` declares.
vpiHandle OnlyPrimitiveArray(vpiHandle scope) {
  vpiHandle it = vpi_iterate(vpiPrimitiveArray, scope);
  return it == nullptr ? nullptr : vpi_scan(it);
}

// §28.3.6: a scalar terminal connects to every element whole, and a terminal
// as wide as the array gives each element its bit, a constant as a named
// vector does: 2'b01 gives element 0 the constant 1 and element 1 the
// constant 0. The constant was connected whole, both elements reading 2'b01.
TEST_F(InstanceArraysOfARun, AGateArraysConstantTerminalIsSharedOutPerElement) {
  Run("module top; wire [1:0] y; logic c;\n"
      "  and g[1:0] (y, 2'b01, c);\n"
      "endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top"));
  ASSERT_NE(array, nullptr);
  const std::vector<vpiHandle> kTerms0 = TermsOf(vpi_handle_by_index(array, 0));
  const std::vector<vpiHandle> kTerms1 = TermsOf(vpi_handle_by_index(array, 1));
  ASSERT_EQ(kTerms0.size(), 3U);
  ASSERT_EQ(kTerms1.size(), 3U);
  vpiHandle bit0 = vpi_handle(vpiExpr, kTerms0[1]);
  vpiHandle bit1 = vpi_handle(vpiExpr, kTerms1[1]);
  EXPECT_EQ(vpi_get(vpiType, bit0), vpiConstant);
  EXPECT_EQ(vpi_get(vpiType, bit1), vpiConstant);
  EXPECT_EQ(IntOf(bit0), 1);
  EXPECT_EQ(IntOf(bit1), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms0[2])),
            VpiObjectOf(By("top.c")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms1[2])),
            VpiObjectOf(By("top.c")));
}

// §28.3.5: a range whose two bounds are equal declares one instance, and its
// one-bit terminals connect to it whole.
TEST_F(InstanceArraysOfARun, AOneElementGateArrayTakesItsTerminalsWhole) {
  Run("module top; wire y; logic a, b;\n"
      "  and g[0:0] (y, a, b);\n"
      "endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top"));
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, array), 1);
  vpiHandle out = FirstTerm(vpi_handle_by_index(array, 0));
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, out)), VpiObjectOf(By("top.y")));
}

// A gate array an instance below the top declares connects each element to
// the bit of that instance's own vector.
TEST_F(InstanceArraysOfARun, AGateArrayBelowTheTopTakesItsInstancesBits) {
  Run("module sub; wire [1:0] y; logic [1:0] a, b;\n"
      "  and g[1:0] (y, a, b);\n"
      "endmodule\n"
      "module top; sub s(); endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top.s"));
  ASSERT_NE(array, nullptr);
  vpiHandle out = FirstTerm(vpi_handle_by_index(array, 1));
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, out)),
            VpiObjectOf(vpi_handle_by_index(By("top.s.y"), 1)));
}

// §37.11: an instance array of switches is a switch array over switches.
TEST_F(InstanceArraysOfARun, ASwitchInstanceArrayIsASwitchArray) {
  Run("module top; wire [1:0] o; logic [1:0] i; logic c;\n"
      "  nmos m[1:0] (o, i, c);\n"
      "endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top"));
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, array), vpiSwitchArray);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(array, 0)), vpiSwitch);
}

// §11.5.1 makes a read outside a vector's bounds legal, yielding x. A gate
// array whose terminal is such a select still gives each element a prim term
// per terminal, whatever the model has for the select itself, and the other
// terminals reach what they connect.
TEST_F(InstanceArraysOfARun, AnElementKeepsEveryTerminalOfAnOutOfRangeSelect) {
  Run("module top; wire [1:0] y; logic [1:0] v; logic c;\n"
      "  and g[1:0] (y, v[5], c);\n"
      "endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top"));
  ASSERT_NE(array, nullptr);
  const std::vector<vpiHandle> kTerms = TermsOf(vpi_handle_by_index(array, 0));
  ASSERT_EQ(kTerms.size(), 3U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[2])),
            VpiObjectOf(By("top.c")));
}

// The figure: an instance array reaches its elements through the `instance`
// class, which groups the kinds an element is.
TEST_F(InstanceArraysOfARun, AnInstanceArrayIteratesItsInstances) {
  Run("module sub; endmodule\n"
      "module top; sub arr[1:0] (); endmodule\n");
  EXPECT_EQ(NamesOf(vpiInstance, By("top.arr")),
            (std::vector<std::string>{"arr[0]", "arr[1]"}));
}

// The full name of what `assign` reaches through vpiLhs, and the value of
// what it reaches through vpiRhs.
struct AssignOf {
  std::string lhs;
  int rhs;
  bool operator==(const AssignOf&) const = default;
};

std::vector<AssignOf> ParamAssignsOf(vpiHandle array) {
  std::vector<AssignOf> assigns;
  vpiHandle it = vpi_iterate(vpiParamAssign, array);
  while (vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it)) {
    vpiHandle lhs = vpi_handle(vpiLhs, assign);
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(vpi_handle(vpiRhs, assign), &value);
    assigns.push_back({lhs == nullptr ? "" : vpi_get_str(vpiFullName, lhs),
                       value.value.integer});
  }
  return assigns;
}

// The figure with §23.10.2: a module array reaches a param assign per
// parameter value assignment its instantiation writes, assigning the
// parameter of the leftmost element by name or, written in order, in the
// order the module declares its parameters, a local parameter being none of
// them (§6.20.4). `.Q()` assigns no value (§23.10.2.2) and is no param
// assign.
TEST_F(InstanceArraysOfARun, AModuleArrayReachesItsParamAssigns) {
  Run("module sub #(parameter int P = 1, parameter int Q = 2); endmodule\n"
      "module ord; parameter int A = 1; localparam int L = 3;\n"
      "  parameter int B = 2; endmodule\n"
      "module top; wire w;\n"
      "  sub #(.P(5), .Q()) s[1:0] ();\n"
      "  ord #(7, 8) o[0:1] ();\n"
      "  sub one ();\n"
      "endmodule\n");
  EXPECT_EQ(ParamAssignsOf(By("top.s")),
            (std::vector<AssignOf>{{"top.s[1].P", 5}}));
  EXPECT_EQ(ParamAssignsOf(By("top.o")),
            (std::vector<AssignOf>{{"top.o[0].A", 7}, {"top.o[0].B", 8}}));
}

// The primitive array of `kind` that `scope` declares, null for none.
vpiHandle PrimitiveArrayOfKind(vpiHandle scope, int kind) {
  vpiHandle it = vpi_iterate(vpiPrimitiveArray, scope);
  while (vpiHandle array = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpi_get(vpiType, array) == kind) return array;
  }
  return nullptr;
}

// The figure with §29.8: an array of UDP instances is a udp array over a udp
// per element, each reaching its udp defn and the array, and the array
// reaching the delay every element is instantiated with; a gate array reaches
// its delay too, and a gate of no array reaches no primitive array.
TEST_F(InstanceArraysOfARun, AUdpArrayIsAnObjectOverItsUdps) {
  Run("primitive my_and(o, a, b);\n"
      "  output o;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 ? : 0;\n"
      "    ? 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire [1:0] y, z; wire lone_out; logic [1:0] a, b;\n"
      "  my_and #3 u[1:0] (y, a, b);\n"
      "  and #(2, 4) g[1:0] (z, a, b);\n"
      "  and lone (lone_out, a[0], b[0]);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle udps = PrimitiveArrayOfKind(top, vpiUdpArray);
  ASSERT_NE(udps, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, udps), "u");
  EXPECT_EQ(vpi_get(vpiSize, udps), 2);
  vpiHandle u1 = vpi_handle_by_index(udps, 1);
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, u1), vpiUdp);
  EXPECT_NE(vpi_handle(vpiUdpDefn, u1), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitiveArray, u1)), VpiObjectOf(udps));
  vpiHandle delay = vpi_handle(vpiDelay, udps);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(VpiObjectOf(delay), VpiObjectOf(vpi_handle(vpiDelay, u1)));
  vpiHandle gates = PrimitiveArrayOfKind(top, vpiGateArray);
  ASSERT_NE(gates, nullptr);
  vpiHandle gate_delay = vpi_handle(vpiDelay, gates);
  ASSERT_NE(gate_delay, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, gate_delay), vpiListOp);
  vpiHandle g0 = vpi_handle_by_index(gates, 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitiveArray, g0)), VpiObjectOf(gates));
  vpiHandle it = vpi_iterate(vpiPrimitive, top);
  vpiHandle lone = nullptr;
  while (vpiHandle prim = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* name = vpi_get_str(vpiName, prim);
    if (name != nullptr && std::string(name) == "lone") lone = prim;
  }
  ASSERT_NE(lone, nullptr);
  EXPECT_EQ(vpi_handle(vpiPrimitiveArray, lone), nullptr);
}

// Detail 2: an array of instances of two dimensions is one module array over
// all its elements, reaching a range per dimension, leftmost first, and its
// leftmost dimension's bounds through vpiLeftRange and vpiRightRange.
TEST_F(InstanceArraysOfARun, AModuleArrayReachesARangePerDimension) {
  Run("module sub; endmodule\n"
      "module top; sub u[1:0][2:4] (); endmodule\n");
  vpiHandle it = vpi_iterate(vpiModuleArray, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle u = vpi_scan(it);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(KindsOf(vpiModule, u).size(), 6U);
  std::vector<std::pair<int, int>> bounds;
  for (vpiHandle range : ObjectsOf(vpiRange, u)) {
    bounds.emplace_back(IntOf(vpi_handle(vpiLeftRange, range)),
                        IntOf(vpi_handle(vpiRightRange, range)));
  }
  EXPECT_EQ(bounds, (std::vector<std::pair<int, int>>{{1, 0}, {2, 4}}));
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, u)), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, u)), 0);
}

// Detail 1: an instance array reaches through vpiExpr a vpiListOp operation
// whose operands are the connections the instantiation wrote to the array, as
// written rather than as each element's share; a port it left unconnected adds
// none.
TEST_F(InstanceArraysOfARun, AnInstanceArrayReachesTheConnectionsWritten) {
  Run("module sub (input a, output o); assign o = a; endmodule\n"
      "module top; logic w; wire [1:0] y, z;\n"
      "  sub u[1:0] (.a(w), .o(y));\n"
      "  sub v[1:0] (.a(), .o(z));\n"
      "endmodule\n");
  vpiHandle list = vpi_handle(vpiExpr, By("top.u"));
  ASSERT_NE(list, nullptr);
  EXPECT_EQ(vpi_get(vpiType, list), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, list), vpiListOp);
  std::vector<std::string> operands;
  for (vpiHandle operand : ObjectsOf(vpiOperand, list)) {
    operands.emplace_back(vpi_get_str(vpiName, operand));
  }
  EXPECT_EQ(operands, (std::vector<std::string>{"w", "y"}));
  vpiHandle unconnected = vpi_handle(vpiExpr, By("top.v"));
  ASSERT_NE(unconnected, nullptr);
  EXPECT_EQ(ObjectsOf(vpiOperand, unconnected).size(), 1U);
}

// §38.19: an index select of an instance array names an element alone, never
// the operation of its connections or a param assign, so an index no element
// of `s[2:1]` stands at selects nothing.
TEST_F(InstanceArraysOfARun, AnIndexSelectOfAnInstanceArrayNamesAnElement) {
  Run("module sub #(parameter int P = 1) (input a); endmodule\n"
      "module top; logic w;\n"
      "  sub #(.P(5)) s[2:1] (.a(w));\n"
      "endmodule\n");
  vpiHandle s = By("top.s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(s, 1)),
            VpiObjectOf(By("top.s[1]")));
  EXPECT_EQ(vpi_handle_by_index(s, 0), nullptr);
}

// The figure's access by index with §38.20: an element of a two-dimensional
// array of instances is named by both its indices at once, u[1][3] by {1, 3},
// and a pair naming no element names nothing. §38.19: one index names no
// instance of such an array, while it names an element of a one-dimensional
// one, by multiple index too.
TEST_F(InstanceArraysOfARun, AnElementIsNamedByEveryIndex) {
  Run("module sub; endmodule\n"
      "module top; sub u[1:0][2:4] (); sub w[1:0] (); endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  PLI_INT32 element[] = {1, 3};
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_multi_index(u, 2, element)),
            VpiObjectOf(By("top.u[1][3]")));
  PLI_INT32 none[] = {1, 5};
  EXPECT_EQ(vpi_handle_by_multi_index(u, 2, none), nullptr);
  EXPECT_EQ(vpi_handle_by_index(u, 1), nullptr);
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  PLI_INT32 first[] = {0};
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_multi_index(w, 1, first)),
            VpiObjectOf(By("top.w[0]")));
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(w, 1)),
            VpiObjectOf(By("top.w[1]")));
}

}  // namespace
}  // namespace delta
