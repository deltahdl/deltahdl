#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.3.8 (Managing transient objects). A handle got during an object's life is
// valid only while the object exists, so a static object's handle can be kept
// for good, while a transient object's handle is either released after use or
// left to be released, and to lapse, when the object goes away.
//
// The subclause's own rule is the second paragraph: callbacks, which differ
// with the kind of object, let an application follow a transient object's
// life, followed by the list of which callbacks those are -
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
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &frame);
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
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &thread);
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
  EXPECT_EQ(VpiObjectOf(g_objects[0]), &class_object);
  EXPECT_EQ(VpiObjectOf(g_objects[1]), &class_object);
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

// The ending half of the list, against a run: the initial procedure's thread
// and the fork branch it spawns end, and the frame its call activated ends
// before them, so cbEndOfThread and cbEndOfFrame each report a transient
// object's end. §37.2.2 item 2 has those ends release the handles to the frame
// and the threads, which the routines were handed while they were still live.
// The branch was made an object as it began (cbStartOfThread), the initial
// procedure's thread only as it ends.
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

// The design below makes a class object and drops it, so the garbage
// collector's next pass reclaims it.
constexpr const char* kDroppedObject =
    "module t;\n"
    "  class C;\n"
    "    int x;\n"
    "  endclass\n"
    "  C c;\n"
    "  initial begin\n"
    "    c = new;\n"
    "    c = null;\n"
    "  end\n"
    "endmodule\n";

// Runs kDroppedObject and then the garbage collector.
void RunAndCollect() {
  SimFixture f;
  auto* design = ElaborateSrc(kDroppedObject, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  f.ctx.CollectGarbage();
}

// Reclaiming the object delivers cbReclaimObj and cbEndOfObject and, by
// §37.2.2 item 3, releases the handle cbCreateObj was given for the object...
TEST_F(TransientObjectCallbacks, ReclaimingARunsObjectDeliversBothReasons) {
  RegisterFor(cbCreateObj);
  RegisterFor(cbReclaimObj);
  RegisterFor(cbEndOfObject);
  RunAndCollect();
  EXPECT_EQ(g_reasons,
            (std::vector<int>{cbCreateObj, cbReclaimObj, cbEndOfObject}));
  ASSERT_FALSE(g_objects.empty());
  EXPECT_TRUE(ctx_.HandleReleased(VpiObjectOf(g_objects[0])));
}

// ...each reason delivered to an application that registered for it alone,
// though no handle to the object was handed out before...
TEST_F(TransientObjectCallbacks, ReclaimingDeliversReclaimObjAlone) {
  RegisterFor(cbReclaimObj);
  RunAndCollect();
  EXPECT_EQ(g_reasons, (std::vector<int>{cbReclaimObj}));
}

TEST_F(TransientObjectCallbacks, ReclaimingDeliversEndOfObjectAlone) {
  RegisterFor(cbEndOfObject);
  RunAndCollect();
  EXPECT_EQ(g_reasons, (std::vector<int>{cbEndOfObject}));
}

// ...and nothing told to an application that registered for neither.
TEST_F(TransientObjectCallbacks, ReclaimingTellsNoOneWhoDidNotAsk) {
  RegisterFor(cbEndOfFrame);
  RunAndCollect();
  EXPECT_TRUE(g_reasons.empty());
}

}  // namespace
}  // namespace delta
