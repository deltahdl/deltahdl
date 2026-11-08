#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleMultiSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle SharedObject(int type, VpiHandle ref1, VpiHandle ref2) {
    VpiHandle obj = vpi_ctx_.CreateModule("shared", "shared");
    obj->type = type;
    ref1->children.push_back(obj);
    ref2->children.push_back(obj);
    return obj;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiHandleMultiSim, ReturnsTheObjectBothReferencesReach) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  EXPECT_EQ(VpiObjectOf(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                                         VpiHandleOf(in_port))),
            path);
}

TEST_F(VpiHandleMultiSim, TheReturnedHandleIsTheObjectItself) {
  auto* mod = vpi_ctx_.CreateModule("d", "d");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  vpiHandle h = vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                                 VpiHandleOf(in_port));
  ASSERT_NE(h, nullptr);

  s_vpi_time in[2] = {};
  in[0].real = 4.0;
  in[1].real = 6.0;
  s_vpi_delay put = {};
  put.da = in;
  put.no_of_delays = 2;
  put.time_type = vpiScaledRealTime;
  vpi_put_delays(h, &put);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(path), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 4.0);
  EXPECT_DOUBLE_EQ(out[1].real, 6.0);
}

TEST_F(VpiHandleMultiSim, NoHandleForAnObjectOnlyOneReferenceReaches) {
  auto* mod1 = vpi_ctx_.CreateModule("m1", "m1");
  vpi_ctx_.CreatePort("p1", kVpiInput, mod1);

  auto* mod2 = vpi_ctx_.CreateModule("m2", "m2");
  vpi_ctx_.CreatePort("p2", kVpiOutput, mod2);

  EXPECT_EQ(vpi_handle_multi(vpiPort, VpiHandleOf(mod1), VpiHandleOf(mod2)),
            nullptr);
}

TEST_F(VpiHandleMultiSim, HandleMultiBothNullReturnsNull) {
  vpiHandle h = vpi_handle_multi(vpiPort, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

TEST_F(VpiHandleMultiSim, HandleMultiOneNullReturnsNull) {
  auto* mod = vpi_ctx_.CreateModule("solo", "solo");
  vpi_ctx_.CreatePort("p", kVpiInput, mod);

  EXPECT_EQ(vpi_handle_multi(vpiPort, VpiHandleOf(mod), nullptr), nullptr);
}

TEST_F(VpiHandleMultiSim, InterModPathRejectsDifferentlySizedPorts) {
  auto* mod = vpi_ctx_.CreateModule("top2", "top2");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  out_port->size = 8;
  in_port->size = 4;
  SharedObject(vpiInterModPath, out_port, in_port);

  vpiHandle h = vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                                 VpiHandleOf(in_port));
  EXPECT_EQ(h, nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiHandleMultiSim, SizeMismatchIgnoredForNonInterModPathType) {
  auto* mod1 = vpi_ctx_.CreateModule("u1", "u1");
  mod1->size = 8;
  auto* mod2 = vpi_ctx_.CreateModule("u2", "u2");
  mod2->size = 4;
  VpiHandle shared = SharedObject(vpiPort, mod1, mod2);

  EXPECT_EQ(VpiObjectOf(vpi_handle_multi(vpiPort, VpiHandleOf(mod1),
                                         VpiHandleOf(mod2))),
            shared);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiHandleMultiSim, InterModPathAcceptsSameSizedPortsAcrossHierarchy) {
  auto* mod_a = vpi_ctx_.CreateModule("a", "top.a");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod_a);
  auto* mod_b = vpi_ctx_.CreateModule("b", "top.a.b");
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod_b);
  out_port->size = 16;
  in_port->size = 16;
  VpiHandle path = SharedObject(vpiInterModPath, out_port, in_port);

  EXPECT_EQ(VpiObjectOf(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                                         VpiHandleOf(in_port))),
            path);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiHandleMultiSim, NoHandleWhenTheSharedObjectIsOfAnotherType) {
  auto* mod = vpi_ctx_.CreateModule("t", "t");
  auto* out_port = vpi_ctx_.CreatePort("o", kVpiOutput, mod);
  auto* in_port = vpi_ctx_.CreatePort("i", kVpiInput, mod);
  SharedObject(vpiPort, out_port, in_port);

  EXPECT_EQ(vpi_handle_multi(vpiInterModPath, VpiHandleOf(out_port),
                             VpiHandleOf(in_port)),
            nullptr);
}

}  // namespace
}  // namespace delta
