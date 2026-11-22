#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr std::string_view kKey = "lookup-by-name-key";

std::string SealedInstanceSource() {
  const std::string kAuthored =
      "`pragma protect begin\n"
      "`pragma protect viewport = (object = \"secret.open_r\", access = "
      "\"r\")\n"
      "module secret;\n"
      "  logic [7:0] open_r;\n"
      "  logic [7:0] shut;\n"
      "endmodule\n"
      "`pragma protect end\n"
      "module t;\n"
      "  logic [7:0] plain;\n"
      "  secret u();\n"
      "  initial $noop;\n"
      "endmodule\n";
  return EncryptEnvelopes(kAuthored, kKey);
}

struct Lookup {
  vpiHandle handle = nullptr;
  bool error = false;
};

class LookupThroughASealedScope : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$noop");
    data.calltf = &VpiDesignRunCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    RunUnderKey(SealedInstanceSource(), kKey, f_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static Lookup Find(const char* name, vpiHandle scope) {
    Lookup lookup;
    lookup.handle = vpi_handle_by_name(VpiText(name), scope);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    lookup.error = kLevel != 0;
    return lookup;
  }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(LookupThroughASealedScope, ANameFromTheTopThroughASealedScopeIsAnError) {
  const Lookup kShut = Find("t.u.shut", nullptr);
  EXPECT_EQ(kShut.handle, nullptr);
  EXPECT_TRUE(kShut.error);
  const Lookup kPlain = Find("t.plain", nullptr);
  EXPECT_NE(kPlain.handle, nullptr);
  EXPECT_FALSE(kPlain.error);
}

TEST_F(LookupThroughASealedScope,
       ANameRelativeToAScopeThroughASealedOneIsAnError) {
  const Lookup kTop = Find("t", nullptr);
  ASSERT_NE(kTop.handle, nullptr);
  const Lookup kShut = Find("u.shut", kTop.handle);
  EXPECT_EQ(kShut.handle, nullptr);
  EXPECT_TRUE(kShut.error);
  const Lookup kPlain = Find("plain", kTop.handle);
  EXPECT_NE(kPlain.handle, nullptr);
  EXPECT_FALSE(kPlain.error);
}

TEST_F(LookupThroughASealedScope, ASealedScopeGivenAsTheScopeIsAnError) {
  const Lookup kSealed = Find("t.u", nullptr);
  ASSERT_NE(kSealed.handle, nullptr);
  const Lookup kShut = Find("shut", kSealed.handle);
  EXPECT_EQ(kShut.handle, nullptr);
  EXPECT_TRUE(kShut.error);
}

TEST_F(LookupThroughASealedScope, ANameEndingAtTheSealedScopeReachesIt) {
  const Lookup kSealed = Find("t.u", nullptr);
  ASSERT_NE(kSealed.handle, nullptr);
  EXPECT_FALSE(kSealed.error);
  EXPECT_EQ(vpi_get(vpiIsProtected, kSealed.handle), 1);
}

TEST_F(LookupThroughASealedScope, AnObjectAViewportOpensIsReachedThroughIt) {
  const Lookup kOpen = Find("t.u.open_r", nullptr);
  EXPECT_NE(kOpen.handle, nullptr);
  EXPECT_FALSE(kOpen.error);
}

}  // namespace
}  // namespace delta
