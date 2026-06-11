#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.37.1: file-scope capture for the systf callback applications. The
// invocation helper passes the registration's user_data field as the single
// PLI_BYTE8 * argument, so each stub records the pointer it received.
const char* g_seen_arg = nullptr;
int g_call_count = 0;

int RecordingCalltf(const char* arg) {
  g_seen_arg = arg;
  ++g_call_count;
  return 0;
}

int SizetfReturning17(const char* arg) {
  g_seen_arg = arg;
  ++g_call_count;
  return 17;
}

// -----------------------------------------------------------------------------
// §38.37.1 tfname rule: the name shall begin with '$' and be followed by one or
// more characters legal in a SystemVerilog simple identifier.
// -----------------------------------------------------------------------------

TEST(VpiSystfCallbacksSim, NameRuleAcceptsWellFormedNames) {
  EXPECT_TRUE(VpiSystfNameIsValid("$measure"));
  EXPECT_TRUE(VpiSystfNameIsValid("$a"));
  EXPECT_TRUE(VpiSystfNameIsValid("$_legal1$"));
}

TEST(VpiSystfCallbacksSim, NameRuleRejectsMissingOrBareDollar) {
  // "one or more" characters must follow the '$': a null pointer, the empty
  // string, a bare "$", and a name with no leading '$' all fail.
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

// -----------------------------------------------------------------------------
// §38.37.1: RegisterSystf applies the tfname rule when registering.
// -----------------------------------------------------------------------------

class VpiSystfCallbacksRegistration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiSystfCallbacksRegistration, RejectsBareDollarName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$";

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, RejectsIllegalCharacterName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$bad-name";

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, RejectsNullName) {
  // A registration carrying no tfname has no "$ + one or more characters" name
  // at all, so the registration is refused (no callback object, nothing stored).
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = nullptr;

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiSystfCallbacksRegistration, AcceptsWellFormedName) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$good_name";

  EXPECT_NE(vpi_register_systf(&data), nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1u);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$good_name");
}

// -----------------------------------------------------------------------------
// §38.37.1 type field: registers the application as a system task or function.
// -----------------------------------------------------------------------------

TEST_F(VpiSystfCallbacksRegistration, TypeFieldStoresTaskOrFunc) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$as_task";

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.tfname = "$as_func";

  vpi_register_systf(&task);
  vpi_register_systf(&func);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2u);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

// -----------------------------------------------------------------------------
// §38.37.1 sysfunctype field: names the return-value kind of a system function,
// and is meaningful only when the type is vpiSysFunc.
// -----------------------------------------------------------------------------

TEST(VpiSystfCallbacksSim, ReturnTypeReportedForSystemFunction) {
  VpiSystfData func = {};
  func.type = kVpiSysFunc;
  func.sysfunctype = kVpiRealFunc;

  EXPECT_EQ(VpiSystfReturnType(func), kVpiRealFunc);
}

TEST(VpiSystfCallbacksSim, ReturnTypeNotReportedForSystemTask) {
  // sysfunctype shall only be used when type is vpiSysFunc, so a task reports no
  // return-value kind even if the field happens to be populated.
  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.sysfunctype = kVpiIntFunc;

  EXPECT_EQ(VpiSystfReturnType(task), 0);
}

// -----------------------------------------------------------------------------
// §38.37.1 sizetf rule: called only for a sized system function; absent sizetf
// makes a sized function 32 bits wide.
// -----------------------------------------------------------------------------

TEST(VpiSystfCallbacksSim, SizetfCalledOnlyForSizedFunction) {
  VpiSystfData sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  EXPECT_TRUE(VpiSystfSizetfIsCalled(sized));

  VpiSystfData sized_signed = {};
  sized_signed.type = kVpiSysFunc;
  sized_signed.sysfunctype = kVpiSizedSignedFunc;
  EXPECT_TRUE(VpiSystfSizetfIsCalled(sized_signed));

  VpiSystfData int_func = {};
  int_func.type = kVpiSysFunc;
  int_func.sysfunctype = kVpiIntFunc;
  EXPECT_FALSE(VpiSystfSizetfIsCalled(int_func));

  // A system task never calls sizetf, even if a sized kind is left in the field.
  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.sysfunctype = kVpiSizedFunc;
  EXPECT_FALSE(VpiSystfSizetfIsCalled(task));
}

TEST(VpiSystfCallbacksSim, SizedFunctionWithSizetfUsesItsWidth) {
  g_seen_arg = nullptr;
  g_call_count = 0;
  int payload = 0;

  VpiSystfData sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = &SizetfReturning17;
  sized.user_data = &payload;

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 17);
  EXPECT_EQ(g_call_count, 1);
  // The sizetf received user_data as its single PLI_BYTE8 * argument.
  EXPECT_EQ(g_seen_arg, reinterpret_cast<const char*>(&payload));
}

TEST(VpiSystfCallbacksSim, SizedFunctionWithoutSizetfDefaultsTo32) {
  VpiSystfData sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = nullptr;

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 32);
}

TEST(VpiSystfCallbacksSim, NonSizedFunctionDoesNotCallSizetf) {
  g_call_count = 0;

  // sizetf is provided but the function is not a sized kind, so it must not be
  // called; the width falls through to the default.
  VpiSystfData int_func = {};
  int_func.type = kVpiSysFunc;
  int_func.sysfunctype = kVpiIntFunc;
  int_func.sizetf = &SizetfReturning17;

  EXPECT_EQ(VpiSystfResultSizeBits(int_func), 32);
  EXPECT_EQ(g_call_count, 0);
}

// -----------------------------------------------------------------------------
// §38.37.1 callback applications: user_data is the only argument (PLI_BYTE8 *),
// a null field is skipped, and compiletf/sizetf fire at build while calltf fires
// each invocation.
// -----------------------------------------------------------------------------

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
  // One or more of the routine fields may be left null when not needed.
  EXPECT_EQ(VpiSystfInvoke(nullptr, &payload), 0);
}

TEST(VpiSystfCallbacksSim, CallbackFiringTimes) {
  // compiletf and sizetf fire while the data structure is compiled/built.
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCompiletf));
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kSizetf));
  // calltf fires each time the task/function is invoked during execution.
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

}  // namespace
}  // namespace delta
