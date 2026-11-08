#include <gtest/gtest.h>

#include <string_view>
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

class ExpressionsWithSideEffects : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(ExpressionsWithSideEffects, GetValueEvaluatesTheSideEffect) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.has_side_effects = true;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(VpiHandleOf(&call), &value);
  EXPECT_EQ(call.side_effect_count, 1);

  vpi_get_value(VpiHandleOf(&call), &value);
  EXPECT_EQ(call.side_effect_count, 2);
}

TEST_F(ExpressionsWithSideEffects,
       GetValueOnPlainExpressionEvaluatesNoSideEffect) {
  VpiObject expr;
  expr.type = vpiOperation;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(VpiHandleOf(&expr), &value);
  EXPECT_EQ(expr.side_effect_count, 0);
  EXPECT_FALSE(VpiExpressionHasSideEffects(&expr));
}

TEST_F(ExpressionsWithSideEffects, GetPropertyNeedingSideEffectEvalIsAnError) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&call)), vpiUndefined);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(call.side_effect_count, 0);
}

TEST_F(ExpressionsWithSideEffects, GetTypeIsAllowedOnSuchAnExpression) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&call)), vpiFuncCall);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST_F(ExpressionsWithSideEffects,
       HandleRelationNeedingSideEffectEvalIsAnError) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&call)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

TEST_F(ExpressionsWithSideEffects, PutValueWithSideEffectingIndexIsAnError) {
  VpiObject post_inc;
  post_inc.type = vpiOperation;
  post_inc.has_side_effects = true;

  VpiObject select;
  select.type = vpiReg;
  select.index_expressions.push_back(&post_inc);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  EXPECT_EQ(vpi_put_value(VpiHandleOf(&select), &value, nullptr, vpiNoDelay),
            nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(post_inc.side_effect_count, 0);
}

TEST_F(ExpressionsWithSideEffects,
       PutValueWithLaterSideEffectingIndexIsAnError) {
  VpiObject leading;
  leading.type = vpiConstant;

  VpiObject pre_dec;
  pre_dec.type = vpiOperation;
  pre_dec.has_side_effects = true;

  VpiObject select;
  select.type = vpiReg;
  select.index_expressions.push_back(&leading);
  select.index_expressions.push_back(&pre_dec);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  EXPECT_EQ(vpi_put_value(VpiHandleOf(&select), &value, nullptr, vpiNoDelay),
            nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(pre_dec.side_effect_count, 0);
}

TEST_F(ExpressionsWithSideEffects, PutValueWithPlainIndexIsNotRefused) {
  VpiObject constant;
  constant.type = vpiConstant;

  VpiObject select;
  select.type = vpiReg;
  select.index_expressions.push_back(&constant);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  vpi_put_value(VpiHandleOf(&select), &value, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

TEST(SideEffectClassification, TheFormsTheSubclauseLists) {
  SimFixture f;

  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("i++", f)));
  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("--i", f)));
  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("(j = 3)", f)));
  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("(j += 3)", f)));

  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("a + (i++)", f)));
  EXPECT_TRUE(VpiSourceExprHasSideEffects(ParseExprFrom("my_array[i++]", f)));

  EXPECT_FALSE(VpiSourceExprHasSideEffects(ParseExprFrom("a + b", f)));
  EXPECT_FALSE(VpiSourceExprHasSideEffects(ParseExprFrom("my_array[k]", f)));
  EXPECT_FALSE(VpiSourceExprHasSideEffects(nullptr));
}

bool g_arg_has_side_effects = false;
int g_arg_side_effect_count = -1;

PLI_INT32 ProbeArgumentCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiArgument, call);
  if (itr == nullptr) return 0;
  vpiHandle arg = vpi_scan(itr);
  if (arg == nullptr) return 0;

  g_arg_has_side_effects = VpiExpressionHasSideEffects(VpiObjectOf(arg));
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(arg, &value);
  g_arg_side_effect_count = VpiObjectOf(arg)->side_effect_count;
  return 0;
}

TEST(SideEffectClassification, ASystemTaskArgumentCarriesItsSideEffects) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_arg_has_side_effects = false;
  g_arg_side_effect_count = -1;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeArgumentCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    $probe(i++);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_TRUE(g_arg_has_side_effects);
  EXPECT_EQ(g_arg_side_effect_count, 1);

  SetGlobalVpiContext(nullptr);
}

bool RefusedForASideEffectingIndex() {
  s_vpi_error_info info = {};
  if (vpi_chk_error(&info) == 0 || info.message == nullptr) return false;
  return std::string_view(info.message)
             .find(
                 "index expression with side "
                 "effects") != std::string_view::npos;
}

void PutThree(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 3;
  vpi_put_value(obj, &value, nullptr, vpiNoDelay);
}

std::vector<bool> g_args_refused;

PLI_INT32 PutEachArgumentCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle itr = call == nullptr ? nullptr : vpi_iterate(vpiArgument, call);
  if (itr == nullptr) return 0;
  while (vpiHandle arg = vpi_scan(itr)) {
    if (vpi_get(vpiOpType, arg) == vpiNullOp) {
      g_args_refused.push_back(false);
      continue;
    }
    PutThree(arg);
    g_args_refused.push_back(RefusedForASideEffectingIndex());
  }
  return 0;
}

TEST(SideEffectingIndexDesign,
     APutThroughAnArgumentsSideEffectingIndexIsRefused) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_args_refused.clear();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$put_each");
  data.calltf = &PutEachArgumentCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer i;\n"
      "  int a[4];\n"
      "  bit [3:0] b[4];\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    $put_each(a[i++], , b[i--][1], a[i]);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_args_refused, (std::vector<bool>{true, false, true, false}));

  SetGlobalVpiContext(nullptr);
}

class SideEffectingIndexOfARun : public VpiDesignRun {
 protected:
  static vpiHandle RhsOfProcess(vpiHandle scope, int n) {
    vpiHandle it = vpi_iterate(vpiProcess, scope);
    vpiHandle proc = it == nullptr ? nullptr : vpi_scan(it);
    for (int i = 0; i < n && proc != nullptr; ++i) proc = vpi_scan(it);
    if (proc == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_handle(vpiStmt, proc));
  }
};

TEST_F(SideEffectingIndexOfARun,
       APutThroughAStatementsSideEffectingIndexIsRefused) {
  Run("module top;\n"
      "  int a[4], x, y, i;\n"
      "  initial x = a[i++];\n"
      "  initial y = a[i];\n"
      "endmodule\n");
  vpiHandle side_effecting = RhsOfProcess(By("top"), 0);
  vpiHandle plain = RhsOfProcess(By("top"), 1);
  ASSERT_NE(side_effecting, nullptr);
  ASSERT_NE(plain, nullptr);
  PutThree(side_effecting);
  EXPECT_TRUE(RefusedForASideEffectingIndex());
  PutThree(plain);
  EXPECT_FALSE(RefusedForASideEffectingIndex());
}

}  // namespace
}  // namespace delta
