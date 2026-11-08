#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<int> g_reasons;
std::vector<vpiHandle> g_objects;

int RecordTransientEvent(s_cb_data* data) {
  g_reasons.push_back(data->reason);
  g_objects.push_back(data->obj);
  return 0;
}

class TransientObjectCallbacks : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_reasons.clear();
    g_objects.clear();
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void RegisterFor(int reason, vpiHandle on = nullptr) {
    s_cb_data data = {};
    data.reason = reason;
    data.cb_rtn = &RecordTransientEvent;
    data.obj = on;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
  }

  VpiContext ctx_;
};

TEST_F(TransientObjectCallbacks, FreeingAFrameDeliversEndOfFrame) {
  RegisterFor(cbEndOfFrame);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx_.ReleaseFrameOrThreadObject(&frame);

  ASSERT_EQ(g_reasons.size(), 1u);
  EXPECT_EQ(g_reasons[0], cbEndOfFrame);
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &frame);
}

TEST_F(TransientObjectCallbacks, FreeingAThreadDeliversEndOfThreadOnly) {
  RegisterFor(cbEndOfThread);
  RegisterFor(cbEndOfFrame);

  VpiObject thread;
  thread.type = vpiThread;
  ctx_.ReleaseFrameOrThreadObject(&thread);

  ASSERT_EQ(g_reasons.size(), 1u);
  EXPECT_EQ(g_reasons[0], cbEndOfThread);
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &thread);
}

TEST_F(TransientObjectCallbacks, ReclaimingAClassObjectDeliversBothReasons) {
  VpiObject class_object;
  class_object.type = vpiClassObj;
  RegisterFor(cbReclaimObj, VpiHandleOf(&class_object));
  RegisterFor(cbEndOfObject);

  ctx_.ReleaseClassObject(&class_object);

  ASSERT_EQ(g_reasons.size(), 2u);
  EXPECT_EQ(g_reasons[0], cbReclaimObj);
  EXPECT_EQ(g_reasons[1], cbEndOfObject);
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &class_object);
  EXPECT_EQ(VpiObjectOf(g_objects[1]), &class_object);
}

TEST_F(TransientObjectCallbacks, AnUnrelatedReasonIsNotDelivered) {
  RegisterFor(cbEndOfSimulation);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx_.ReleaseFrameOrThreadObject(&frame);

  EXPECT_TRUE(g_reasons.empty());
}

TEST_F(TransientObjectCallbacks, ARunDeliversTheStartOfAThreadAndAFrame) {
  RegisterFor(cbStartOfThread);
  RegisterFor(cbStartOfFrame);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function integer f(input integer x);\n"
      "    f = x + 1;\n"
      "  endfunction\n"
      "  integer r;\n"
      "  initial r = f(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ctx_.RefreshThreadObjects();

  int threads = 0;
  int frames = 0;
  for (int reason : g_reasons) {
    if (reason == cbStartOfThread) ++threads;
    if (reason == cbStartOfFrame) ++frames;
  }
  EXPECT_GT(threads, 0);
  EXPECT_GT(frames, 0);
}

TEST_F(TransientObjectCallbacks, ARunDeliversTheEndOfAThreadAndAFrame) {
  RegisterFor(cbStartOfThread);
  RegisterFor(cbEndOfThread);
  RegisterFor(cbEndOfFrame);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function integer f(input integer x);\n"
      "    f = x + 1;\n"
      "  endfunction\n"
      "  integer r;\n"
      "  initial fork r = f(1); join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  int threads = 0;
  int frames = 0;
  for (size_t i = 0; i < g_reasons.size(); ++i) {
    if (g_reasons[i] == cbStartOfThread) continue;
    if (g_reasons[i] == cbEndOfThread) ++threads;
    if (g_reasons[i] == cbEndOfFrame) ++frames;
    EXPECT_TRUE(ctx_.HandleReleased(VpiObjectOf(g_objects[i])));
  }
  EXPECT_GE(threads, 2);
  EXPECT_GT(frames, 0);
}

constexpr const char* kDroppedObject =
    "module t;\n"
    "  class C;\n"
    "    int x;\n"
    "  endclass\n"
    "  C c;\n"
    "  initial begin\n"
    "    $arm;\n"
    "    c = new;\n"
    "    c = null;\n"
    "  end\n"
    "endmodule\n";

std::vector<int> g_armed;

PLI_INT32 ArmCalltf(PLI_BYTE8*) {
  vpiHandle spec =
      vpi_handle(vpiTypespec, vpi_handle_by_name(VpiText("t.c"), nullptr));
  for (int reason : g_armed) {
    s_cb_data data = {};
    data.reason = reason;
    data.cb_rtn = &RecordTransientEvent;
    data.obj = spec;
    vpi_register_cb(&data);
  }
  return 0;
}

void RunAndCollect(const std::vector<int>& armed = {}) {
  g_armed = armed;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$arm");
  task.calltf = &ArmCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  auto* design = ElaborateSrc(kDroppedObject, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  f.ctx.CollectGarbage();
}

TEST_F(TransientObjectCallbacks, ReclaimingARunsObjectDeliversBothReasons) {
  RegisterFor(cbEndOfObject);
  RunAndCollect({cbCreateObj, cbReclaimObj});
  EXPECT_EQ(g_reasons,
            (std::vector<int>{cbCreateObj, cbReclaimObj, cbEndOfObject}));
  ASSERT_FALSE(g_objects.empty());
  EXPECT_TRUE(ctx_.HandleReleased(VpiObjectOf(g_objects[0])));
}

TEST_F(TransientObjectCallbacks, ReclaimingDeliversReclaimObjAlone) {
  RunAndCollect({cbReclaimObj});
  EXPECT_EQ(g_reasons, (std::vector<int>{cbReclaimObj}));
}

TEST_F(TransientObjectCallbacks, ReclaimingDeliversEndOfObjectAlone) {
  RegisterFor(cbEndOfObject);
  RunAndCollect();
  EXPECT_EQ(g_reasons, (std::vector<int>{cbEndOfObject}));
}

TEST_F(TransientObjectCallbacks, ReclaimingTellsNoOneWhoDidNotAsk) {
  RegisterFor(cbEndOfFrame);
  RunAndCollect();
  EXPECT_TRUE(g_reasons.empty());
}

}  // namespace
}  // namespace delta
