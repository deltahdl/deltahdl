#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3811Test : public ::testing::Test {
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

// §38.11: vpi_get_str

TEST_F(VpiClause3811Test, GetStrNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "top_mod");
}

TEST_F(VpiClause3811Test, GetStrFullNameForModule) {
  vpi_ctx_.CreateModule("top_mod", "lib.top_mod");
  vpiHandle h = vpi_handle_by_name("top_mod", nullptr);
  ASSERT_NE(h, nullptr);

  const char* full = vpi_get_str(vpiFullName, h);
  ASSERT_NE(full, nullptr);
  EXPECT_STREQ(full, "lib.top_mod");
}

TEST_F(VpiClause3811Test, GetStrDefNameForModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  const char* def = vpi_get_str(vpiDefName, h);
  ASSERT_NE(def, nullptr);
  EXPECT_STREQ(def, "dut");
}

TEST_F(VpiClause3811Test, GetStrReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_str(vpiName, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
