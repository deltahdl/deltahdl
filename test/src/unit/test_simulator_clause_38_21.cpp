#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleByNameSim : public ::testing::Test {
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

TEST_F(VpiHandleByNameSim, HandleByNameFindsModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name("dut", nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiModule);
}

TEST_F(VpiHandleByNameSim, HandleByNameNullReturnsNullptr) {
  vpiHandle h = vpi_handle_by_name(nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// §38.21 C6: when a scope is provided the search is confined to that scope's
// contents. A child resolves through its parent scope, while a top-level object
// that is not within the scope is not found via that scope.
TEST_F(VpiHandleByNameSim, ScopeConfinesSearch) {
  vpi_ctx_.CreateModule("alpha", "alpha");  // top-level, outside `top`
  vpiHandle top = vpi_ctx_.CreateModule("top", "top");
  vpiHandle beta = vpi_ctx_.CreatePort("beta", kVpiInput, top);

  EXPECT_EQ(vpi_handle_by_name("beta", top), beta);
  EXPECT_EQ(vpi_handle_by_name("alpha", top), nullptr);
}

// §38.21 C4: the name may be hierarchical. A dotted path is walked component by
// component, descending from the top-level scope into its children.
TEST_F(VpiHandleByNameSim, HierarchicalNameResolves) {
  vpiHandle top = vpi_ctx_.CreateModule("top", "top");
  vpiHandle beta = vpi_ctx_.CreatePort("beta", kVpiInput, top);

  EXPECT_EQ(vpi_handle_by_name("top.beta", nullptr), beta);
}

// §38.21 C7: calling vpi_handle_by_name() for a protected scope object is an
// error - no handle is returned and the error is recorded.
TEST_F(VpiHandleByNameSim, ProtectedScopeIsError) {
  vpiHandle locked = vpi_ctx_.CreateModule("sec", "sec");
  locked->is_protected = true;
  vpi_ctx_.CreatePort("inner", kVpiInput, locked);

  EXPECT_EQ(vpi_handle_by_name("inner", locked), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.21 C8: a hierarchical name that passes through a protected scope is an
// error; the protected intermediate scope cannot be descended into.
TEST_F(VpiHandleByNameSim, HierarchicalThroughProtectedScopeIsError) {
  vpiHandle root = vpi_ctx_.CreateModule("root", "root");
  vpiHandle mid = vpi_ctx_.CreatePort("mid", kVpiInput, root);
  mid->is_protected = true;
  vpi_ctx_.CreatePort("deep", kVpiInput, mid);

  EXPECT_EQ(vpi_handle_by_name("root.mid.deep", nullptr), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

}  // namespace
}  // namespace delta
