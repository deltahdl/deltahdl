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

TEST(InstanceArrayModel, InstanceArrayTypeClassification) {
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiInstanceArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiModuleArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiInterfaceArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiProgramArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiPrimitiveArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiGateArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiSwitchArray));
  EXPECT_TRUE(VpiIsInstanceArrayType(vpiUdpArray));
  EXPECT_FALSE(VpiIsInstanceArrayType(vpiModule));
}

TEST(InstanceArrayModel, PrimitiveArrayTypeClassification) {
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiPrimitiveArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiGateArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiSwitchArray));
  EXPECT_TRUE(VpiIsPrimitiveArrayType(vpiUdpArray));
  EXPECT_FALSE(VpiIsPrimitiveArrayType(vpiModuleArray));
  EXPECT_FALSE(VpiIsPrimitiveArrayType(vpiModule));
}

TEST(InstanceArrayModel, ConnectionsAreTheOperationChild) {
  VpiObject array;
  array.type = vpiModuleArray;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  array.children.push_back(&op);

  EXPECT_EQ(VpiInstanceArrayConnections(&array), &op);
  EXPECT_EQ(VpiInstanceArrayConnections(nullptr), nullptr);
  VpiObject single_module;
  single_module.type = vpiModule;
  single_module.children.push_back(&op);
  EXPECT_EQ(VpiInstanceArrayConnections(&single_module), nullptr);
  VpiObject empty_array;
  empty_array.type = vpiModuleArray;
  EXPECT_EQ(VpiInstanceArrayConnections(&empty_array), nullptr);
}

TEST(InstanceArrayModel, ConnectionsSkipNonOperationChildren) {
  VpiObject array;
  array.type = vpiInterfaceArray;
  VpiObject leading;
  leading.type = vpiRange;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  array.children.push_back(&leading);
  array.children.push_back(&op);

  EXPECT_EQ(VpiInstanceArrayConnections(&array), &op);
}

TEST(InstanceArrayModel, ConnectionExprIsListOperation) {
  VpiObject list_op;
  list_op.type = vpiOperation;
  list_op.op_type = vpiListOp;
  EXPECT_TRUE(VpiInstanceArrayConnectionsIsListOp(&list_op));

  VpiObject other_op;
  other_op.type = vpiOperation;
  other_op.op_type = vpiConcatOp;
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(&other_op));
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(&constant));
  EXPECT_FALSE(VpiInstanceArrayConnectionsIsListOp(nullptr));
}

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

  VpiObject single;
  single.type = vpiModule;
  single.children.push_back(&op);
  EXPECT_EQ(ctx.Handle(vpiExpr, &single), nullptr);

  SetGlobalVpiContext(nullptr);
}

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

TEST(InstanceArrayModel, RangesRunLeftmostToRightmost) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims =
      MakeTwoFixedUnpackedDims({&l0, &r0, 4}, {&l1, &r1, 2});

  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_EQ(ranges[0].left_expr, &l0);
  EXPECT_EQ(ranges[0].right_expr, &r0);
  EXPECT_EQ(ranges[1].left_expr, &l1);
  EXPECT_EQ(ranges[1].right_expr, &r1);

  EXPECT_TRUE(VpiInstanceArrayRanges({}).empty());
}

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

  EXPECT_EQ(VpiInstanceArrayLeftRange({}), nullptr);
  EXPECT_EQ(VpiInstanceArrayRightRange({}), nullptr);
}

TEST(InstanceArrayModel, EmptyLeftmostRangeReportsNullBounds) {
  VpiObject l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kQueue;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;

  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_TRUE(ranges[0].empty);
  EXPECT_EQ(VpiInstanceArrayLeftRange(dims), nullptr);
  EXPECT_EQ(VpiInstanceArrayRightRange(dims), nullptr);
}

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

class InstanceArraysOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static vpiHandle FirstTerm(vpiHandle prim) {
    vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

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

TEST_F(InstanceArraysOfARun, AnInterfaceArrayIsAnInterfaceArray) {
  Run("interface ifc; endinterface\n"
      "module top; ifc ifs[0:1] (); endmodule\n");
  vpiHandle ifs = By("top.ifs");
  ASSERT_NE(ifs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ifs), vpiInterfaceArray);
  EXPECT_EQ(vpi_get(vpiSize, ifs), 2);
}

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

std::vector<vpiHandle> TermsOf(vpiHandle prim) {
  std::vector<vpiHandle> terms;
  vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
  while (vpiHandle term = it == nullptr ? nullptr : vpi_scan(it)) {
    terms.push_back(term);
  }
  return terms;
}

vpiHandle OnlyPrimitiveArray(vpiHandle scope) {
  vpiHandle it = vpi_iterate(vpiPrimitiveArray, scope);
  return it == nullptr ? nullptr : vpi_scan(it);
}

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

TEST_F(InstanceArraysOfARun, ASubarrayOrElementTerminalReachesEachElementsBit) {
  Run("module top; wire [1:0][1:0] p; logic [1:0] mem [0:1];\n"
      "  wire [1:0] y, z;\n"
      "  buf g[1:0] (y, p[1]);\n"
      "  buf h[1:0] (z, mem[1]);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiGateArray, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle g = vpi_scan(it);
  vpiHandle h = vpi_scan(it);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(h, nullptr);
  if (std::string(vpi_get_str(vpiName, g)) == "h") std::swap(g, h);
  vpiHandle element = vpi_handle_by_index(By("top.mem"), 1);
  ASSERT_NE(element, nullptr);
  for (int k = 0; k < 2; ++k) {
    const std::vector<vpiHandle> kG = TermsOf(vpi_handle_by_index(g, k));
    const std::vector<vpiHandle> kH = TermsOf(vpi_handle_by_index(h, k));
    ASSERT_EQ(kG.size(), 2U);
    ASSERT_EQ(kH.size(), 2U);
    vpiHandle p_bit = vpi_handle(vpiExpr, kG[1]);
    ASSERT_NE(p_bit, nullptr);
    EXPECT_EQ(vpi_get(vpiType, p_bit), vpiNetBit) << k;
    EXPECT_EQ(std::string(vpi_get_str(vpiName, p_bit)),
              "p[1][" + std::to_string(k) + "]");
    vpiHandle mem_bit = vpi_handle(vpiExpr, kH[1]);
    ASSERT_NE(mem_bit, nullptr);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, mem_bit)), VpiObjectOf(element))
        << k;
    EXPECT_EQ(IntOf(vpi_handle(vpiIndex, mem_bit)), k);
  }
}

TEST_F(InstanceArraysOfARun, ABitwiseTerminalReachesAnOperationOfEachBit) {
  Run("module top; wire [1:0] a, b, y, z;\n"
      "  buf g[1:0] (y, a & b);\n"
      "  buf h[1:0] (z, ~a);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiGateArray, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle g = vpi_scan(it);
  vpiHandle h = vpi_scan(it);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(h, nullptr);
  if (std::string(vpi_get_str(vpiName, g)) == "h") std::swap(g, h);
  for (int k = 0; k < 2; ++k) {
    const std::vector<vpiHandle> kG = TermsOf(vpi_handle_by_index(g, k));
    const std::vector<vpiHandle> kH = TermsOf(vpi_handle_by_index(h, k));
    ASSERT_EQ(kG.size(), 2U);
    ASSERT_EQ(kH.size(), 2U);
    vpiHandle and_op = vpi_handle(vpiExpr, kG[1]);
    EXPECT_EQ(OpOf(and_op), vpiBitAndOp) << k;
    const std::vector<vpiHandle> kAnd = OperandsOf(and_op);
    ASSERT_EQ(kAnd.size(), 2U);
    EXPECT_EQ(VpiObjectOf(kAnd[0]),
              VpiObjectOf(vpi_handle_by_index(By("top.a"), k)));
    EXPECT_EQ(VpiObjectOf(kAnd[1]),
              VpiObjectOf(vpi_handle_by_index(By("top.b"), k)));
    vpiHandle neg_op = vpi_handle(vpiExpr, kH[1]);
    EXPECT_EQ(OpOf(neg_op), vpiBitNegOp) << k;
    const std::vector<vpiHandle> kNeg = OperandsOf(neg_op);
    ASSERT_EQ(kNeg.size(), 1U);
    EXPECT_EQ(VpiObjectOf(kNeg[0]),
              VpiObjectOf(vpi_handle_by_index(By("top.a"), k)));
  }
}

TEST_F(InstanceArraysOfARun, ASwitchInstanceArrayIsASwitchArray) {
  Run("module top; wire [1:0] o; logic [1:0] i; logic c;\n"
      "  nmos m[1:0] (o, i, c);\n"
      "endmodule\n");
  vpiHandle array = OnlyPrimitiveArray(By("top"));
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, array), vpiSwitchArray);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(array, 0)), vpiSwitch);
}

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

TEST_F(InstanceArraysOfARun, AnInstanceArrayIteratesItsInstances) {
  Run("module sub; endmodule\n"
      "module top; sub arr[1:0] (); endmodule\n");
  EXPECT_EQ(NamesOf(vpiInstance, By("top.arr")),
            (std::vector<std::string>{"arr[0]", "arr[1]"}));
}

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

vpiHandle PrimitiveArrayOfKind(vpiHandle scope, int kind) {
  vpiHandle it = vpi_iterate(vpiPrimitiveArray, scope);
  while (vpiHandle array = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpi_get(vpiType, array) == kind) return array;
  }
  return nullptr;
}

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

TEST_F(InstanceArraysOfARun, ANestedModulesArraysReachTheirParamAssigns) {
  Run("module sub #(parameter int P = 1); endmodule\n"
      "module top;\n"
      "  module inner #(parameter int W = 1, parameter int D = 2);\n"
      "    sub #(.P(6)) s[1:0] ();\n"
      "  endmodule\n"
      "  inner #(4, 5) n[1:0] ();\n"
      "  inner m ();\n"
      "endmodule\n");
  EXPECT_EQ(ParamAssignsOf(By("top.n")),
            (std::vector<AssignOf>{{"top.n[1].W", 4}, {"top.n[1].D", 5}}));
  EXPECT_EQ(ParamAssignsOf(By("top.m.s")),
            (std::vector<AssignOf>{{"top.m.s[1].P", 6}}));
}

}  // namespace
}  // namespace delta
