#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(SourceDelayModel, DelayCarryingTypeClassification) {
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiNet));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiPrimitive));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiGate));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiSwitch));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiUdp));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiModPath));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiTchk));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiContAssign));
  EXPECT_FALSE(VpiObjectCarriesSourceDelay(vpiModule));
}

TEST(SourceDelayModel, SingleDelayReachesConstantExpression) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject delay;
  delay.type = vpiConstant;
  net.delay_expr = &delay;

  EXPECT_EQ(VpiSourceDelayExpr(&net), &delay);
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(VpiSourceDelayExpr(&net)));
}

TEST(SourceDelayModel, NoDelayExpressionReachesNull) {
  EXPECT_EQ(VpiSourceDelayExpr(nullptr), nullptr);

  VpiObject delay;
  delay.type = vpiConstant;

  VpiObject module;
  module.type = vpiModule;
  module.delay_expr = &delay;
  EXPECT_EQ(VpiSourceDelayExpr(&module), nullptr);

  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(VpiSourceDelayExpr(&net), nullptr);
}

TEST(SourceDelayModel, MultipleDelaysAreListOperation) {
  VpiObject list_op;
  list_op.type = vpiOperation;
  list_op.op_type = vpiListOp;
  EXPECT_TRUE(VpiSourceDelayExprIsListOp(&list_op));

  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(&constant));

  VpiObject other_op;
  other_op.type = vpiOperation;
  other_op.op_type = vpiConcatOp;
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(&other_op));
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(nullptr));
}

TEST(SourceDelayPublic, HandleDelayReturnsSingleConstantExpression) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject delay;
  delay.type = vpiConstant;
  cont_assign.delay_expr = &delay;

  VpiHandle expr = ctx.Handle(vpiDelay, &cont_assign);
  ASSERT_EQ(expr, &delay);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiConstant);
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(expr));

  SetGlobalVpiContext(nullptr);
}

TEST(SourceDelayPublic, HandleDelayReturnsListOperationForMultipleDelays) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject mod_path;
  mod_path.type = vpiModPath;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  mod_path.delay_expr = &op;

  VpiHandle expr = ctx.Handle(vpiDelay, &mod_path);
  ASSERT_EQ(expr, &op);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiOperation);
  EXPECT_EQ(ctx.Get(vpiOpType, expr), vpiListOp);
  EXPECT_TRUE(VpiSourceDelayExprIsListOp(expr));

  SetGlobalVpiContext(nullptr);
}

TEST(SourceDelayPublic, HandleDelayNotDivertedForNonDelayObject) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject delay;
  delay.type = vpiConstant;
  VpiObject module;
  module.type = vpiModule;
  module.delay_expr = &delay;

  EXPECT_EQ(ctx.Handle(vpiDelay, &module), nullptr);

  SetGlobalVpiContext(nullptr);
}

int g_one_delay_type = 0;
int g_two_delay_type = 0;
int g_two_delay_op_type = 0;
int g_two_delay_operands = 0;

PLI_INT32 ProbeSourceDelaysCalltf(PLI_BYTE8*) {
  vpiHandle one = vpi_handle_by_name(VpiText("m1.s"), nullptr);
  vpiHandle two = vpi_handle_by_name(VpiText("m1.w"), nullptr);
  if (one == nullptr || two == nullptr) return 0;

  if (vpiHandle expr = vpi_handle(vpiDelay, one)) {
    g_one_delay_type = vpi_get(vpiType, expr);
  }
  vpiHandle list = vpi_handle(vpiDelay, two);
  if (list == nullptr) return 0;
  g_two_delay_type = vpi_get(vpiType, list);
  g_two_delay_op_type = vpi_get(vpiOpType, list);
  if (vpiHandle itr = vpi_iterate(vpiOperand, list)) {
    while (vpi_scan(itr) != nullptr) ++g_two_delay_operands;
  }
  return 0;
}

void RegisterSourceDelayProbe() {
  g_one_delay_type = 0;
  g_two_delay_type = 0;
  g_two_delay_op_type = 0;
  g_two_delay_operands = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeSourceDelaysCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST(SourceDelayDesign, ANetsDeclaredDelaysAreReachedThroughVpiDelay) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  RegisterSourceDelayProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire #(3, 5) w;\n"
      "  wire #7 s;\n"
      "  assign w = 1'b0;\n"
      "  assign s = 1'b0;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_one_delay_type, vpiConstant);
  EXPECT_EQ(g_two_delay_type, vpiOperation);
  EXPECT_EQ(g_two_delay_op_type, vpiListOp);
  EXPECT_EQ(g_two_delay_operands, 2);

  SetGlobalVpiContext(nullptr);
}

class SourceDelaysOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("primitive inv(output o, input i);\n"
        "  table 0 : 1; 1 : 0; endtable\n"
        "endprimitive\n"
        "module m(input a, input b, output o, output y);\n"
        "  wire p, q, n;\n"
        "  tri r;\n"
        "  and #(2, 3) g(o, a, b);\n"
        "  buf #4 g1(y, a);\n"
        "  inv #(14, 15) u(n, a);\n"
        "  assign #5 p = a;\n"
        "  assign #(6, 7) q = b;\n"
        "  assign #(16, 17, 18) r = a;\n"
        "  specify\n"
        "    (a => o) = (8, 9);\n"
        "    (b => y) = 10;\n"
        "    $setup(a, posedge b, 11);\n"
        "    $setuphold(posedge b, a, 12, 13);\n"
        "  endspecify\n"
        "endmodule\n"
        "module top; reg a, b; wire o, y; m m1(a, b, o, y); endmodule\n");
  }

  static std::vector<int> DelaysOf(vpiHandle obj) {
    vpiHandle delay = vpi_handle(vpiDelay, obj);
    if (delay == nullptr) return {};
    if (vpi_get(vpiType, delay) == vpiConstant) return {ValueOf(delay)};
    if (vpi_get(vpiOpType, delay) != vpiListOp) return {-1};
    std::vector<int> values;
    vpiHandle it = vpi_iterate(vpiOperand, delay);
    while (vpiHandle operand = vpi_scan(it)) {
      values.push_back(
          vpi_get(vpiType, operand) == vpiConstant ? ValueOf(operand) : -1);
    }
    return values;
  }

  static int ValueOf(vpiHandle constant) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(constant, &value);
    return value.value.integer;
  }

  static std::vector<vpiHandle> AllOf(int type) {
    std::vector<vpiHandle> found;
    vpiHandle it = vpi_iterate(type, By("top.m1"));
    if (it == nullptr) return found;
    while (vpiHandle obj = vpi_scan(it)) found.push_back(obj);
    return found;
  }
};

TEST_F(SourceDelaysOfARun, APrimitivesWrittenDelaysAreReached) {
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top.m1"), "g")),
            (std::vector<int>{2, 3}));
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top.m1"), "g1")),
            (std::vector<int>{4}));
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top.m1"), "u")),
            (std::vector<int>{14, 15}));
}

TEST_F(SourceDelaysOfARun, AContinuousAssignmentsWrittenDelaysAreReached) {
  std::vector<std::vector<int>> delays;
  for (vpiHandle assign : AllOf(vpiContAssign)) {
    delays.push_back(DelaysOf(assign));
  }
  std::ranges::sort(delays);
  EXPECT_EQ(delays, (std::vector<std::vector<int>>{{5}, {6, 7}, {16, 17, 18}}));
}

TEST_F(SourceDelaysOfARun, AModulePathsWrittenDelaysAreReached) {
  std::vector<std::vector<int>> delays;
  for (vpiHandle path : AllOf(vpiModPath)) delays.push_back(DelaysOf(path));
  std::ranges::sort(delays);
  EXPECT_EQ(delays, (std::vector<std::vector<int>>{{8, 9}, {10}}));
}

TEST_F(SourceDelaysOfARun, ATimingChecksWrittenLimitsAreReached) {
  std::vector<std::vector<int>> delays;
  for (vpiHandle check : AllOf(vpiTchk)) delays.push_back(DelaysOf(check));
  std::ranges::sort(delays);
  EXPECT_EQ(delays, (std::vector<std::vector<int>>{{11}, {12, 13}}));
}

}  // namespace
}  // namespace delta
