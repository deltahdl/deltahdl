#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/lexical_limits.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

const char* g_seen_arg = nullptr;
int g_call_count = 0;

PLI_INT32 RecordingCalltf(PLI_BYTE8* arg) {
  g_seen_arg = arg;
  ++g_call_count;
  return 0;
}

PLI_INT32 SizetfReturning17(PLI_BYTE8* arg) {
  g_seen_arg = arg;
  ++g_call_count;
  return 17;
}

TEST(VpiSystfCallbacksSim, NameRuleAcceptsWellFormedNames) {
  EXPECT_TRUE(VpiSystfNameIsValid("$measure"));
  EXPECT_TRUE(VpiSystfNameIsValid("$a"));
  EXPECT_TRUE(VpiSystfNameIsValid("$_legal1$"));
}

TEST(VpiSystfCallbacksSim, NameRuleRejectsMissingOrBareDollar) {
  EXPECT_FALSE(VpiSystfNameIsValid(nullptr));
  EXPECT_FALSE(VpiSystfNameIsValid(""));
  EXPECT_FALSE(VpiSystfNameIsValid("$"));
  EXPECT_FALSE(VpiSystfNameIsValid("measure"));
}

TEST(VpiSystfCallbacksSim, NameRuleRejectsIllegalTrailingCharacters) {
  EXPECT_FALSE(VpiSystfNameIsValid("$has-dash"));
  EXPECT_FALSE(VpiSystfNameIsValid("$has space"));
  EXPECT_FALSE(VpiSystfNameIsValid("$dot.name"));
}

class VpiSystfCallbacksRegistration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiSystfCallbacksRegistration, RejectsBareDollarName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$");

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, RejectsIllegalCharacterName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$bad-name");

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, RejectsNullName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = nullptr;

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, AcceptsWellFormedName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$good_name");

  EXPECT_NE(vpi_register_systf(&data), nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1u);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$good_name");
}

TEST_F(VpiSystfCallbacksRegistration, AcceptsANameAtTheIdentifierMaximum) {
  std::string name = "$" + std::string(kMaxIdentifierLength - 1, 'a');
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = name.data();

  EXPECT_NE(vpi_register_systf(&data), nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1u);
  EXPECT_EQ(std::string_view(vpi_ctx_.RegisteredSystfs()[0].tfname).size(),
            kMaxIdentifierLength);
}

TEST_F(VpiSystfCallbacksRegistration, RejectsANameBeyondTheIdentifierMaximum) {
  std::string name = "$" + std::string(kMaxIdentifierLength, 'a');
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = name.data();

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_STREQ(info.message,
               "system task or function name exceeds the maximum identifier "
               "length");
}

TEST_F(VpiSystfCallbacksRegistration, TypeFieldStoresTaskOrFunc) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$as_task");

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$as_func");

  vpi_register_systf(&task);
  vpi_register_systf(&func);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2u);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

TEST(VpiSystfCallbacksSim, ReturnTypeReportedForSystemFunction) {
  s_vpi_systf_data func = {};
  func.type = kVpiSysFunc;
  func.sysfunctype = kVpiRealFunc;

  EXPECT_EQ(VpiSystfReturnType(func), kVpiRealFunc);
}

TEST(VpiSystfCallbacksSim, ReturnTypeNotReportedForSystemTask) {
  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.sysfunctype = kVpiIntFunc;

  EXPECT_EQ(VpiSystfReturnType(task), 0);
}

TEST(VpiSystfCallbacksSim, SizetfCalledOnlyForSizedFunction) {
  s_vpi_systf_data sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  EXPECT_TRUE(VpiSystfSizetfIsCalled(sized));

  s_vpi_systf_data sized_signed = {};
  sized_signed.type = kVpiSysFunc;
  sized_signed.sysfunctype = kVpiSizedSignedFunc;
  EXPECT_TRUE(VpiSystfSizetfIsCalled(sized_signed));

  s_vpi_systf_data int_func = {};
  int_func.type = kVpiSysFunc;
  int_func.sysfunctype = kVpiIntFunc;
  EXPECT_FALSE(VpiSystfSizetfIsCalled(int_func));

  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.sysfunctype = kVpiSizedFunc;
  EXPECT_FALSE(VpiSystfSizetfIsCalled(task));
}

TEST(VpiSystfCallbacksSim, SizedFunctionWithSizetfUsesItsWidth) {
  g_seen_arg = nullptr;
  g_call_count = 0;
  int payload = 0;

  s_vpi_systf_data sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = &SizetfReturning17;
  sized.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 17);
  EXPECT_EQ(g_call_count, 1);
  EXPECT_EQ(g_seen_arg, reinterpret_cast<const char*>(&payload));
}

TEST(VpiSystfCallbacksSim, SizedFunctionWithoutSizetfDefaultsTo32) {
  s_vpi_systf_data sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = nullptr;

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 32);
}

TEST(VpiSystfCallbacksSim, SignedSizedFunctionWithoutSizetfDefaultsTo32) {
  s_vpi_systf_data sized_signed = {};
  sized_signed.type = kVpiSysFunc;
  sized_signed.sysfunctype = kVpiSizedSignedFunc;
  sized_signed.sizetf = nullptr;

  EXPECT_EQ(VpiSystfResultSizeBits(sized_signed), 32);
}

TEST(VpiSystfCallbacksSim, NonSizedFunctionDoesNotCallSizetf) {
  g_call_count = 0;

  s_vpi_systf_data int_func = {};
  int_func.type = kVpiSysFunc;
  int_func.sysfunctype = kVpiIntFunc;
  int_func.sizetf = &SizetfReturning17;

  EXPECT_EQ(VpiSystfResultSizeBits(int_func), 32);
  EXPECT_EQ(g_call_count, 0);
}

TEST(VpiSystfCallbacksSim, InvokePassesUserDataAsSingleArgument) {
  g_seen_arg = nullptr;
  g_call_count = 0;
  char payload[1] = {'x'};

  int rc = VpiSystfInvoke(&RecordingCalltf, payload);

  EXPECT_EQ(rc, 0);
  EXPECT_EQ(g_call_count, 1);
  EXPECT_EQ(g_seen_arg, static_cast<const char*>(payload));
}

TEST(VpiSystfCallbacksSim, InvokeSkipsNullCallback) {
  int payload = 0;
  EXPECT_EQ(VpiSystfInvoke(nullptr, reinterpret_cast<PLI_BYTE8*>(&payload)), 0);
}

TEST(VpiSystfCallbacksSim, CallbackFiringTimes) {
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCompiletf));
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kSizetf));
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

PLI_INT32 PutHighOneLowFive(PLI_BYTE8*) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.high = 1;
  time.low = 5;
  s_vpi_value value = {};
  value.format = vpiTimeVal;
  value.value.time = &time;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

PLI_INT32 PutAllOnes(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

PLI_INT32 EightBits(PLI_BYTE8*) { return 8; }

class SystemFunctionResultsOfARun : public VpiDesignRun {
 protected:
  void RegisterFunction(const char* name, int functype,
                        PLI_INT32 (*calltf)(PLI_BYTE8*),
                        PLI_INT32 (*sizetf)(PLI_BYTE8*) = nullptr) {
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = functype;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    data.sizetf = sizetf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static s_vpi_vecval VectorOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiVectorVal;
    vpi_get_value(By(name), &value);
    return value.value.vector != nullptr ? value.value.vector[0]
                                         : s_vpi_vecval{};
  }
};

TEST_F(SystemFunctionResultsOfARun, ATimeFunctionReturnsSixtyFourBits) {
  RegisterFunction("$user_time", vpiTimeFunc, &PutHighOneLowFive);
  Run("module top; time t; initial t = $user_time(); endmodule\n");
  s_vpi_value value = {};
  value.format = vpiTimeVal;
  vpi_get_value(By("top.t"), &value);
  ASSERT_NE(value.value.time, nullptr);
  EXPECT_EQ(value.value.time->high, 1u);
  EXPECT_EQ(value.value.time->low, 5u);
}

TEST_F(SystemFunctionResultsOfARun, ASizedSignedFunctionReturnsASignedValue) {
  RegisterFunction("$user_s8", vpiSizedSignedFunc, &PutAllOnes, &EightBits);
  RegisterFunction("$user_u8", vpiSizedFunc, &PutAllOnes, &EightBits);
  Run("module top; int s, u;\n"
      "  initial begin s = $user_s8(); u = $user_u8(); end\n"
      "endmodule\n");
  EXPECT_EQ(VectorOf("top.s").aval, 0xFFFFFFFFu);
  EXPECT_EQ(VectorOf("top.u").aval, 0xFFu);
}

TEST_F(VpiSystfCallbacksRegistration, RejectsAFunctionOfNoFunctionType) {
  for (const int kFuncType : {0, 99}) {
    s_vpi_systf_data func = {};
    func.type = vpiSysFunc;
    func.sysfunctype = kFuncType;
    func.tfname = VpiText("$untyped");
    EXPECT_EQ(vpi_register_systf(&func), nullptr) << kFuncType;
    EXPECT_NE(vpi_chk_error(nullptr), 0) << kFuncType;
  }
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, AcceptsATaskOfNoFunctionType) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.sysfunctype = 0;
  task.tfname = VpiText("$untyped_task");
  EXPECT_NE(vpi_register_systf(&task), nullptr);
}

}  // namespace
}  // namespace delta
