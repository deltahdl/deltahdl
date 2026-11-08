#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiGetStringSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiGetStringSim, GetStrNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name(VpiText("top_mod"), nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "top_mod");
}

TEST_F(VpiGetStringSim, GetStrFullNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name(VpiText("top_mod"), nullptr);
  ASSERT_NE(h, nullptr);

  const char* full = vpi_get_str(vpiFullName, h);
  ASSERT_NE(full, nullptr);
  EXPECT_STREQ(full, "lib.top_mod");
}

TEST_F(VpiGetStringSim, GetStrDefNameForModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name(VpiText("dut"), nullptr);
  ASSERT_NE(h, nullptr);
  const char* def = vpi_get_str(vpiDefName, h);
  ASSERT_NE(def, nullptr);
  EXPECT_STREQ(def, "dut");
}

TEST_F(VpiGetStringSim, GetStrReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_str(vpiName, nullptr), nullptr);
}

TEST_F(VpiGetStringSim, ResultBufferIsReusedByEveryCall) {
  vpi_ctx_.CreateModule("aaa", "lib.aaa");
  vpi_ctx_.CreateModule("bbb", "lib.bbb");
  vpiHandle a = vpi_handle_by_name(VpiText("aaa"), nullptr);
  vpiHandle b = vpi_handle_by_name(VpiText("bbb"), nullptr);
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  const char* first = vpi_get_str(vpiName, a);
  ASSERT_NE(first, nullptr);
  EXPECT_STREQ(first, "aaa");

  const char* second = vpi_get_str(vpiName, b);
  ASSERT_NE(second, nullptr);
  EXPECT_STREQ(second, "bbb");

  EXPECT_EQ(first, second);
  EXPECT_STREQ(first, "bbb");
}

TEST_F(VpiGetStringSim, ValueStringUsesADifferentBufferFromGetStr) {
  auto* var = sim_ctx_.CreateVariable("v", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4869);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("v"), nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "v");

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);

  EXPECT_NE(static_cast<const void*>(val.value.str),
            static_cast<const void*>(name));
  EXPECT_STREQ(name, "v");
}

TEST_F(VpiGetStringSim, ProtectedObjectIsAnError) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&mod)), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

std::string g_instance_name;
std::string g_definition_name;

PLI_INT32 ReadInstanceNamesCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  const char* name = vpi_get_str(vpiName, mod);
  if (name != nullptr) g_instance_name = name;
  const char* def = vpi_get_str(vpiDefName, mod);
  if (def != nullptr) g_definition_name = def;
  return 0;
}

void RegisterNameProbe() {
  g_instance_name.clear();
  g_definition_name.clear();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadInstanceNamesCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class VpiGetStringInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiGetStringInARun, AnInstanceReportsWhatItIsAnInstanceOf) {
  RegisterNameProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_instance_name, "m1");
  EXPECT_EQ(g_definition_name, "m");
}

TEST_F(VpiGetStringSim, ANetHasNoDefinitionName) {
  VpiObject net;
  net.type = vpiNet;
  net.name = "w";
  EXPECT_EQ(vpi_get_str(vpiDefName, VpiHandleOf(&net)), nullptr);
}

}  // namespace
}  // namespace delta
