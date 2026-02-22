#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3806Test : public ::testing::Test {
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

// §38.6: vpi_get

TEST_F(VpiClause3806Test, GetTypeForModule) {
  auto *mod = vpi_ctx_.CreateModule("m", "m");
  EXPECT_EQ(vpi_get(vpiType, mod), vpiModule);
}

TEST_F(VpiClause3806Test, GetTypeForPort) {
  auto *mod = vpi_ctx_.CreateModule("m", "m");
  auto *port = vpi_ctx_.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiType, port), vpiPort);
}

TEST_F(VpiClause3806Test, GetTypeForParameter) {
  auto *param = vpi_ctx_.CreateParameter("WIDTH", 32);
  EXPECT_EQ(vpi_get(vpiType, param), vpiParameter);
}

TEST_F(VpiClause3806Test, GetTypeForNet) {
  auto *net_obj = vpi_ctx_.CreateNetObj("n", nullptr, 4);
  EXPECT_EQ(vpi_get(vpiType, net_obj), vpiNet);
}

TEST_F(VpiClause3806Test, GetDirectionForPort) {
  auto *mod = vpi_ctx_.CreateModule("m", "m");
  auto *port = vpi_ctx_.CreatePort("din", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiDirection, port), vpiInput);
}

TEST_F(VpiClause3806Test, GetSizeForVariable) {
  auto *var = sim_ctx_.CreateVariable("wide", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("wide", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, h), 32);
}

TEST_F(VpiClause3806Test, GetReturnsZeroForNullHandle) {
  EXPECT_EQ(vpi_get(vpiType, nullptr), 0);
}

}  // namespace
}  // namespace delta
