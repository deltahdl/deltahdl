#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleMultiSim : public ::testing::Test {
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

TEST_F(VpiHandleMultiSim, HandleMultiCombinesChildren) {
  auto* mod1 = vpi_ctx_.CreateModule("m1", "m1");
  vpi_ctx_.CreatePort("p1", kVpiInput, mod1);

  auto* mod2 = vpi_ctx_.CreateModule("m2", "m2");
  vpi_ctx_.CreatePort("p2", kVpiOutput, mod2);

  vpiHandle h = VpiHandleMultiC(vpiPort, mod1, mod2);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(static_cast<int>(h->children.size()), 2);
}

TEST_F(VpiHandleMultiSim, HandleMultiBothNullReturnsNull) {
  vpiHandle h = VpiHandleMultiC(vpiPort, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// §38.22: for a vpiInterModPath request the two reference objects are the
// output and input ports the path runs between, and they shall be of the same
// size. A pair whose widths differ cannot name a valid intermodule path, so the
// routine reports an error (§38.2) and returns no handle.
TEST_F(VpiHandleMultiSim, InterModPathRejectsDifferentlySizedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  out_port->size = 8;
  in_port->size = 4;

  vpiHandle h = VpiHandleMultiC(vpiInterModPath, out_port, in_port);
  EXPECT_EQ(h, nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.22: the same-size requirement is specific to intermodule-path requests.
// For any other object type the routine combines the reference objects without
// inspecting their sizes, so a size mismatch must not turn into an error here.
TEST_F(VpiHandleMultiSim, SizeMismatchIgnoredForNonInterModPathType) {
  auto* mod1 = vpi_ctx_.CreateModule("u1", "u1");
  vpi_ctx_.CreatePort("a", kVpiInput, mod1);
  mod1->size = 8;

  auto* mod2 = vpi_ctx_.CreateModule("u2", "u2");
  vpi_ctx_.CreatePort("b", kVpiOutput, mod2);
  mod2->size = 4;

  vpiHandle h = VpiHandleMultiC(vpiPort, mod1, mod2);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(static_cast<int>(h->children.size()), 2);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.22: ports of the same size are accepted even when they sit at different
// levels of the hierarchy (here, one port per module). The path linked from
// both ports is reached and no error is raised.
TEST_F(VpiHandleMultiSim, InterModPathAcceptsSameSizedPortsAcrossHierarchy) {
  auto* mod_a = vpi_ctx_.CreateModule("a", "top.a");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod_a);
  auto* mod_b = vpi_ctx_.CreateModule("b", "top.a.b");
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod_b);
  out_port->size = 16;
  in_port->size = 16;

  auto* path = vpi_ctx_.CreateModule("path", "path");
  path->type = vpiInterModPath;
  out_port->children.push_back(path);
  in_port->children.push_back(path);

  vpiHandle h = VpiHandleMultiC(vpiInterModPath, out_port, in_port);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
  ASSERT_FALSE(h->children.empty());
  EXPECT_EQ(h->children[0]->type, vpiInterModPath);
}

}  // namespace
}  // namespace delta
