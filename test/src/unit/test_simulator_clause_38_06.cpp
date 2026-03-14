#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetPropertySim : public ::testing::Test {
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

TEST_F(VpiGetPropertySim, GetTypeForModule) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  EXPECT_EQ(vpi_get(vpiType, mod), vpiModule);
}

TEST_F(VpiGetPropertySim, GetTypeForPort) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  auto* port = vpi_ctx_.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiType, port), vpiPort);
}

TEST_F(VpiGetPropertySim, GetTypeForParameter) {
  auto* param = vpi_ctx_.CreateParameter("WIDTH", 32);
  EXPECT_EQ(vpi_get(vpiType, param), vpiParameter);
}

TEST_F(VpiGetPropertySim, GetTypeForNet) {
  auto* net_obj = vpi_ctx_.CreateNetObj("n", nullptr, 4);
  EXPECT_EQ(vpi_get(vpiType, net_obj), vpiNet);
}

TEST_F(VpiGetPropertySim, GetDirectionForPort) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  auto* port = vpi_ctx_.CreatePort("din", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiDirection, port), vpiInput);
}

TEST_F(VpiGetPropertySim, GetSizeForVariable) {
  auto* var = sim_ctx_.CreateVariable("wide", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("wide", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, h), 32);
}

TEST_F(VpiGetPropertySim, GetReturnsZeroForNullHandle) {
  EXPECT_EQ(vpi_get(vpiType, nullptr), 0);
}

}  // namespace
}  // namespace delta
