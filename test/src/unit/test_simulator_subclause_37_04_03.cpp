#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiRelationTraversal : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiRelationTraversal, AOneToOneRelationIsWalkedWithVpiHandle) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle port = ctx_.CreatePort("p", kVpiInput, mod);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, VpiHandleOf(port))), mod);
}

TEST_F(VpiRelationTraversal, AOneToManyRelationIsWalkedWithVpiScan) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiHandle p0 = ctx_.CreatePort("p0", kVpiInput, mod);
  VpiHandle p1 = ctx_.CreatePort("p1", kVpiOutput, mod);

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiPort, VpiHandleOf(mod)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), p0);
  EXPECT_EQ(VpiObjectOf(seen[1]), p1);
}

TEST_F(VpiRelationTraversal, ARelationFromACircleIsTraversedWithANullRef) {
  VpiHandle top = ctx_.CreateModule("top", "top");
  top->top_module = true;

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiModule, nullptr));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), top);
}

TEST_F(VpiRelationTraversal, ARelationFromNoCircleIsNotTraversedFromNull) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  VpiObject reg;
  reg.type = kVpiReg;
  mod->children.push_back(&reg);

  ASSERT_EQ(ScanAll(vpi_iterate(kVpiReg, VpiHandleOf(mod))).size(), 1u);

  EXPECT_EQ(vpi_iterate(kVpiReg, nullptr), nullptr);
}

TEST_F(VpiRelationTraversal, TheOneToOneRoutineAgreesAboutANullRef) {
  VpiHandle mod = ctx_.CreateModule("top", "top");
  mod->top_module = true;

  EXPECT_EQ(vpi_handle(vpiPort, nullptr), nullptr);
}

int g_current_call_type = 0;

PLI_INT32 RecordCurrentCall(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  g_current_call_type = call == nullptr ? 0 : vpi_get(vpiType, call);
  return 0;
}

class RelationTraversalOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_current_call_type = 0;
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$record_call");
    data.calltf = &RecordCurrentCall;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(RelationTraversalOfARun, ATaggedOneToOneRelationIsWalkedByItsTag) {
  Run("module top; wire [3:0] w; endmodule\n");
  vpiHandle net = vpi_handle_by_name(VpiText("top.w"), nullptr);
  ASSERT_NE(net, nullptr);
  vpiHandle left = vpi_handle(vpiLeftRange, net);
  vpiHandle right = vpi_handle(vpiRightRange, net);
  ASSERT_NE(left, nullptr);
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(IntOf(left), 3);
  EXPECT_EQ(IntOf(right), 0);
}

TEST_F(RelationTraversalOfARun, ATaggedOneToManyRelationIsScannedByItsTag) {
  Run("module leaf; endmodule\n"
      "module top; leaf u1(); leaf u2(); endmodule\n");
  vpiHandle top = vpi_handle_by_name(VpiText("top"), nullptr);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiInternalScope, top),
            (std::vector<std::string>{"u1", "u2"}));
}

TEST_F(RelationTraversalOfARun, AOneToOneRelationFromACircleTakesANullRef) {
  Run("module top; initial $record_call; endmodule\n");
  EXPECT_EQ(g_current_call_type, vpiSysTaskCall);
}

TEST_F(RelationTraversalOfARun, AOneToManyRelationFromACircleTakesANullRef) {
  Run("module top; endmodule\n");
  EXPECT_EQ(NamesOf(vpiModule, nullptr), (std::vector<std::string>{"top"}));
}

}  // namespace
}  // namespace delta
