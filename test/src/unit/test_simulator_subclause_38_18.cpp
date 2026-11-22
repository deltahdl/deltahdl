#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleSim : public ::testing::Test {
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

TEST_F(VpiHandleSim, HandleReturnsParentModule) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  auto* port = vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  vpiHandle result = vpi_handle(vpiModule, VpiHandleOf(port));
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(VpiObjectOf(result), mod);
}

TEST_F(VpiHandleSim, DISABLED_AModuleDoesNotAnswerForItsPorts) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("clk", kVpiInput, mod);

  EXPECT_EQ(vpi_handle(vpiPort, VpiHandleOf(mod)), nullptr);
}

TEST_F(VpiHandleSim, HandleReturnsNullptrForNullRef) {
  vpiHandle result = vpi_handle(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleSim, HandleReturnsNullptrForNoMatch) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");

  vpiHandle result = vpi_handle(vpiNet, VpiHandleOf(mod));
  EXPECT_EQ(result, nullptr);
}

TEST_F(VpiHandleSim, HandleProtectedObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("clk", kVpiInput, mod);
  mod->is_protected = true;

  vpiHandle result = vpi_handle(vpiPort, VpiHandleOf(mod));
  EXPECT_EQ(result, nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiHandleSim, ARelationTheReferenceDoesNotDrawIsNull) {
  VpiObject net;
  net.type = vpiNet;
  for (int type : {vpiClassObj, vpiActual, vpiUdpDefn, vpiPattern, vpiIndex,
                   vpiFunction, vpiTchkNotifier, vpiNetTypedefAlias, vpiWith}) {
    EXPECT_EQ(vpi_handle(type, VpiHandleOf(&net)), nullptr) << type;
  }
  VpiObject assertion;
  assertion.type = vpiImmediateAssert;
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&assertion)), nullptr);
}

class RelationsOfARun : public VpiDesignRun {};

TEST_F(RelationsOfARun, ASwitchsTerminalReachesItsSwitch) {
  Run("module top; wire a, b; logic en;\n"
      "  tran t1(a, b); tranif1 t2(a, b, en);\n"
      "endmodule\n");
  for (const char* name : {"t1", "t2"}) {
    vpiHandle sw = Named(vpiPrimitive, By("top"), name);
    ASSERT_NE(sw, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, sw), vpiSwitch) << name;
    const std::vector<vpiHandle> kTerms = ObjectsOf(vpiPrimTerm, sw);
    ASSERT_FALSE(kTerms.empty()) << name;
    for (vpiHandle term : kTerms) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, term)), VpiObjectOf(sw))
          << name;
    }
  }
}

constexpr const char* kChildInstance =
    "module child(input logic i); wire n; endmodule\n"
    "module top; logic i; wire w; child c(i); endmodule\n";

TEST_F(RelationsOfARun, AnInstanceReachesItsParentAlongASingleArrow) {
  Run(kChildInstance);
  vpiHandle port = Named(vpiPort, By("top.c"), "i");
  ASSERT_NE(port, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, port)), VpiObjectOf(By("top.c")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, By("top.c"))),
            VpiObjectOf(By("top")));
}

TEST_F(RelationsOfARun, DISABLED_AOneToManyRelationIsNotFollowed) {
  Run(kChildInstance);
  EXPECT_EQ(vpi_handle(vpiPort, By("top.c")), nullptr);
  EXPECT_EQ(vpi_handle(vpiNet, By("top.c")), nullptr);
  EXPECT_EQ(vpi_handle(vpiNet, By("top")), nullptr);
  EXPECT_EQ(vpi_handle(vpiModule, By("top")), nullptr);
  EXPECT_FALSE(ObjectsOf(vpiPort, By("top.c")).empty());
  EXPECT_FALSE(ObjectsOf(vpiNet, By("top")).empty());
}

}  // namespace
}  // namespace delta
