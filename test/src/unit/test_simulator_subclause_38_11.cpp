#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "top_mod");
}

TEST_F(VpiGetStringSim, GetStrFullNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* full = vpi_get_str(vpiFullName, h);
  ASSERT_NE(full, nullptr);
  EXPECT_STREQ(full, "lib.top_mod");
}

TEST_F(VpiGetStringSim, GetStrDefNameForModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  const char* def = vpi_get_str(vpiDefName, h);
  ASSERT_NE(def, nullptr);
  EXPECT_STREQ(def, "dut");
}

TEST_F(VpiGetStringSim, GetStrReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_str(vpiName, nullptr), nullptr);
}

// §38.11: the result is placed in a single temporary buffer that every call
// reuses, so a pointer handed back by an earlier call is overwritten - and
// reflects the new value - once a later call runs.
TEST_F(VpiGetStringSim, ResultBufferIsReusedByEveryCall) {
  vpi_ctx_.CreateModule("aaa", "lib.aaa");
  vpi_ctx_.CreateModule("bbb", "lib.bbb");
  vpiHandle a = vpi_handle_by_name("aaa", nullptr);
  vpiHandle b = vpi_handle_by_name("bbb", nullptr);
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  const char* first = vpi_get_str(vpiName, a);
  ASSERT_NE(first, nullptr);
  EXPECT_STREQ(first, "aaa");

  const char* second = vpi_get_str(vpiName, b);
  ASSERT_NE(second, nullptr);
  EXPECT_STREQ(second, "bbb");

  // Both results come from the one shared buffer, so the earlier pointer now
  // reads the later call's value.
  EXPECT_EQ(first, second);
  EXPECT_STREQ(first, "bbb");
}

// §38.11: a different buffer backs strings returned through the s_vpi_value
// structure, so retrieving a value string does not disturb a string previously
// handed back by vpi_get_str().
TEST_F(VpiGetStringSim, ValueStringUsesADifferentBufferFromGetStr) {
  auto* var = sim_ctx_.CreateVariable("v", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4869);  // encodes "Hi"
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("v", nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "v");

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);

  // The value string occupies separate storage, so the earlier vpi_get_str()
  // pointer is untouched and the two pointers differ.
  EXPECT_NE(static_cast<const void*>(val.value.str),
            static_cast<const void*>(name));
  EXPECT_STREQ(name, "v");
}

// §38.11: unless otherwise specified, calling vpi_get_str() for a protected
// object is an error - it yields no string and records an error.
TEST_F(VpiGetStringSim, ProtectedObjectIsAnError) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.is_protected = true;

  EXPECT_EQ(vpi_get_str(vpiName, &mod), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

// -----------------------------------------------------------------------------
// §38.11's own example:
//
//   vpiHandle mod = vpi_handle_by_name("top.mod1",NULL);
//   vpi_printf ("Module top.mod1 is an instance of %s\n",
//      vpi_get_str(vpiDefName, mod));
//
// What the sentence around it asks of the routine is that vpiDefName say what
// the instance is an instance of. The instance's own name is vpiName and
// answers a different question, and a module reporting that here said that
// mod1 is an instance of mod1.
//
// The cases above build their module objects with VpiContext::CreateModule,
// where the two names are the one string the case passed, so the difference
// between them could not show. These run a design, where an instance and the
// module it instantiates are named apart by construction.
// -----------------------------------------------------------------------------

// What the application read. §38.11 is the reason each is copied at once: "the
// string shall be placed in a temporary buffer that shall be used by every call
// to this routine. If the string is to be used after a subsequent call, the
// string should be copied to another location."
std::string g_instance_name;
std::string g_definition_name;

int ReadInstanceNamesCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
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
  data.tfname = "$probe";
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

  // The instance is named m1 and is an instance of m. Two strings, from one
  // object, through one routine -- which is the example, and which a module
  // reporting its own name for both cannot produce.
  EXPECT_EQ(g_instance_name, "m1");
  EXPECT_EQ(g_definition_name, "m");
}

}  // namespace
}  // namespace delta
