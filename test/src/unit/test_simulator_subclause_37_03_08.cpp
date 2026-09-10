#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.8 (Managing transient objects). "One may obtain a handle to an object
// during its lifetime, and it remains valid only as long as the object exists.
// For a static object, one may therefore keep its handle indefinitely. For a
// transient object, one may release its handle after use or expect that handle
// to be released and become invalid when the object ceases to exist."
//
// The subclause's own rule is the second paragraph: "The life of a transient
// object may be tracked through various callbacks, depending on the specific
// type of object", followed by the list of which callbacks those are -
// cbCreateObj, cbReclaimObj, cbStartofFrame, cbEndOfFrame, cbStartOfThread,
// cbEndOfThread, and cbEndOfObject. So an application that registers one of
// them is called when the life event it names happens to a transient object.
// (The list spells cbStartofFrame with a lowercase "o"; Annex M defines the
// constant as cbStartOfFrame, which is the name used here.)
//
// The validity half of the subclause is §37.2.4's rule, tested there.

// What the application was told. A callback routine is a plain C function with
// no return path to the case that provoked it.
std::vector<int> g_reasons;
std::vector<vpiHandle> g_objects;

int RecordTransientEvent(VpiCbData* data) {
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

  void RegisterFor(int reason) {
    s_cb_data data = {};
    data.reason = reason;
    data.cb_rtn = &RecordTransientEvent;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
  }

  VpiContext ctx_;
};

// The frame half of the list. A frame is freed with its subelements by
// §37.2.2's frame/thread rule, and that is the end of the frame's life, so
// cbEndOfFrame is delivered for it.
TEST_F(TransientObjectCallbacks, FreeingAFrameDeliversEndOfFrame) {
  RegisterFor(cbEndOfFrame);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx_.ReleaseFrameOrThreadObject(&frame);

  ASSERT_EQ(g_reasons.size(), 1u);
  EXPECT_EQ(g_reasons[0], cbEndOfFrame);
  EXPECT_EQ(g_objects[0], &frame);
}

// The thread half of the same rule. The two reasons are told apart by the kind
// of object being freed, so a thread's end is not reported as a frame's.
TEST_F(TransientObjectCallbacks, FreeingAThreadDeliversEndOfThreadOnly) {
  RegisterFor(cbEndOfThread);
  RegisterFor(cbEndOfFrame);

  VpiObject thread;
  thread.type = vpiThread;
  ctx_.ReleaseFrameOrThreadObject(&thread);

  ASSERT_EQ(g_reasons.size(), 1u);
  EXPECT_EQ(g_reasons[0], cbEndOfThread);
  EXPECT_EQ(g_objects[0], &thread);
}

// Reclaiming a class object is the end of that object's life, and the list
// gives it two callbacks: cbReclaimObj for the reclaim and cbEndOfObject for
// the object ceasing to exist. Both are delivered, and both name the object.
TEST_F(TransientObjectCallbacks, ReclaimingAClassObjectDeliversBothReasons) {
  RegisterFor(cbReclaimObj);
  RegisterFor(cbEndOfObject);

  VpiObject class_object;
  class_object.type = vpiClassObj;
  ctx_.ReleaseClassObject(&class_object);

  ASSERT_EQ(g_reasons.size(), 2u);
  EXPECT_EQ(g_reasons[0], cbReclaimObj);
  EXPECT_EQ(g_reasons[1], cbEndOfObject);
  EXPECT_EQ(g_objects[0], &class_object);
  EXPECT_EQ(g_objects[1], &class_object);
}

// An application that registered for none of these life events is not called by
// them, so the delivery above is the registration being honoured rather than
// every callback being run.
TEST_F(TransientObjectCallbacks, AnUnrelatedReasonIsNotDelivered) {
  RegisterFor(cbEndOfSimulation);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx_.ReleaseFrameOrThreadObject(&frame);

  EXPECT_TRUE(g_reasons.empty());
}

// The beginning half of the list, against a run. A thread becomes an object of
// the model when the design's processes are walked, and a frame is activated
// for each call the design makes, so cbStartOfThread and cbStartOfFrame both
// report a transient object beginning its life. Neither was delivered from any
// site, so an application tracking a frame or a thread saw only its end.
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
  // §37.44: the run's processes become thread objects when the set of them is
  // brought up to date, which is what an application iterating vpiThread makes
  // happen. Asking for it directly is the same pass without the iteration.
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

}  // namespace
}  // namespace delta
