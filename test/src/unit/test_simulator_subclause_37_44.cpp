#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.44 thread: the VPI object model for a thread - a SystemVerilog process
// such as an always procedure or a branch of a fork construct (detail 1). The
// diagram gives a thread one Boolean property (vpiActive) and four relations:
// vpiParent reaches the spawning thread, vpiOrigin reaches the originating
// statement, the tagless frame line reaches the thread's active frame, and the
// one-to-many thread relation iterates the threads this thread spawned. These
// tests observe the production helpers in vpi.cpp and VpiContext::Get that
// apply those rules. Thread specific callbacks are §38.36.1's (detail 2).

// vpiActive property: a thread reports whether it is the active one through
// vpi_get(vpiActive).
TEST(ThreadModel, ActiveBooleanPropertyIsReported) {
  VpiContext ctx;

  VpiObject running;
  running.type = vpiThread;
  running.active = true;
  EXPECT_EQ(ctx.Get(vpiActive, &running), 1);

  VpiObject suspended;
  suspended.type = vpiThread;
  EXPECT_EQ(ctx.Get(vpiActive, &suspended), 0);
}

// vpiParent -> thread: a thread reaches the thread that spawned it through its
// parent link.
TEST(ThreadModel, ParentRelationReachesTheSpawningThread) {
  VpiObject parent;
  parent.type = vpiThread;

  VpiObject child;
  child.type = vpiThread;
  child.parent = &parent;

  EXPECT_EQ(VpiThreadParent(&child), &parent);
}

// vpiParent edge: a root thread (no parent) and a null handle report no parent;
// a parent that is not a thread is not reported as a thread parent.
TEST(ThreadModel, ParentRelationIsNullForRootAndNonThreadParents) {
  VpiObject root;
  root.type = vpiThread;
  EXPECT_EQ(VpiThreadParent(&root), nullptr);

  EXPECT_EQ(VpiThreadParent(nullptr), nullptr);

  VpiObject module_scope;
  module_scope.type = vpiModule;
  VpiObject thread_in_module;
  thread_in_module.type = vpiThread;
  thread_in_module.parent = &module_scope;
  EXPECT_EQ(VpiThreadParent(&thread_in_module), nullptr);
}

// vpiOrigin -> stmt: a thread reaches the statement it was started from, held
// apart from its children, and reports none when it was started from none or
// the handle is null.
TEST(ThreadModel, OriginRelationReachesTheOriginatingStatement) {
  VpiObject origin;
  origin.type = vpiBegin;

  VpiObject thread;
  thread.type = vpiThread;
  thread.body = &origin;
  EXPECT_EQ(VpiThreadOrigin(&thread), &origin);

  VpiObject bare;
  bare.type = vpiThread;
  EXPECT_EQ(VpiThreadOrigin(&bare), nullptr);
  EXPECT_EQ(VpiThreadOrigin(nullptr), nullptr);
}

// frame -- thread with §37.43 detail 4: a thread reaches the frame active in
// it now, the innermost active frame of its call chain, passing over a frame
// that has ended, and none when no frame is active.
TEST(ThreadModel, FrameRelationReachesTheActiveFrame) {
  VpiObject inner;
  inner.type = vpiFrame;
  VpiObject outer;
  outer.type = vpiFrame;
  outer.active = true;
  outer.children = {&inner};

  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&outer};
  EXPECT_EQ(VpiThreadFrame(&thread), &outer);
  inner.active = true;
  EXPECT_EQ(VpiThreadFrame(&thread), &inner);
  inner.active = false;
  outer.active = false;
  EXPECT_EQ(VpiThreadFrame(&thread), nullptr);

  VpiObject bare;
  bare.type = vpiThread;
  EXPECT_EQ(VpiThreadFrame(&bare), nullptr);
  EXPECT_EQ(VpiThreadFrame(nullptr), nullptr);
}

// thread one-to-many thread: the iteration yields the threads this thread
// spawned, in order, skipping non-thread children (the origin statement and the
// active frame).
TEST(ThreadModel, ThreadIterationYieldsSpawnedThreads) {
  VpiObject origin;
  origin.type = vpiStmt;
  VpiObject frame;
  frame.type = vpiFrame;
  VpiObject child0;
  child0.type = vpiThread;
  VpiObject child1;
  child1.type = vpiThread;

  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&child0, &origin, &child1, &frame};

  std::vector<VpiHandle> spawned = VpiThreadThreads(&thread);
  ASSERT_EQ(spawned.size(), 2u);
  EXPECT_EQ(spawned[0], &child0);
  EXPECT_EQ(spawned[1], &child1);
}

// thread one-to-many thread edge: a thread that spawned nothing, and a null
// handle, iterate to no threads.
TEST(ThreadModel, ThreadIterationIsEmptyWhenNoneSpawned) {
  VpiObject thread;
  thread.type = vpiThread;
  EXPECT_TRUE(VpiThreadThreads(&thread).empty());
  EXPECT_TRUE(VpiThreadThreads(nullptr).empty());
}

// -----------------------------------------------------------------------------
// §37.44 detail 1: a thread is a SystemVerilog process, an always procedure or
// one branch of a fork for example. Every case above builds its threads by
// hand, which says what the model reports about an object and nothing about
// where such an object comes from -- and no run produced one at all, so the
// whole of this model answered for a design only in a test that wrote the
// design's threads itself.
//
// The cases below run a design and let an application reach the threads it has,
// through the iteration the diagram's circle relation draws: vpi_iterate with a
// null reference.
// -----------------------------------------------------------------------------

// What the application made of the run's threads. A calltf is a plain C
// function with no return path to the case that provoked it.
int g_threads_seen = 0;
int g_non_threads_seen = 0;
int g_threads_with_a_parent = 0;
int g_spawned_total = 0;

PLI_INT32 InspectThreadsCalltf(PLI_BYTE8*) {
  vpiHandle threads = vpi_iterate(vpiThread, nullptr);
  if (threads == nullptr) return 0;
  for (vpiHandle t = vpi_scan(threads); t != nullptr; t = vpi_scan(threads)) {
    ++g_threads_seen;
    if (vpi_get(vpiType, t) != vpiThread) ++g_non_threads_seen;
    if (VpiThreadParent(VpiObjectOf(t)) != nullptr) ++g_threads_with_a_parent;
    g_spawned_total +=
        static_cast<int>(VpiThreadThreads(VpiObjectOf(t)).size());
  }
  return 0;
}

void RegisterThreadProbe() {
  g_threads_seen = 0;
  g_non_threads_seen = 0;
  g_threads_with_a_parent = 0;
  g_spawned_total = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectThreadsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// The clause's two examples in one design: a process, and two branches of a
// fork inside it. The call is written after the join so all three have run by
// the time the application looks.
void RunAForkOfTwoBranches(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  int b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join\n"
      "    $probe;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class ThreadModelInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(ThreadModelInARun, TheRunsThreadsAreReachedByANullReferencedIteration) {
  RegisterThreadProbe();

  SimFixture f;
  RunAForkOfTwoBranches(f);

  // The procedure and the two branches of the fork it ran, which is §37.44
  // detail 1's own list of what a thread is. Before this the iteration answered
  // with nothing whatever the design did, no run having made a thread object.
  EXPECT_GE(g_threads_seen, 3);
  // And every one of them is a thread, rather than the iteration having handed
  // back whatever else the context holds.
  EXPECT_EQ(g_non_threads_seen, 0);
}

TEST_F(ThreadModelInARun, AForkBranchReachesTheThreadThatSpawnedIt) {
  RegisterThreadProbe();

  SimFixture f;
  RunAForkOfTwoBranches(f);

  // §37.44 (vpiParent -> thread, and the one-to-many thread relation): the two
  // branches are the threads with a parent, and the procedure that forked them
  // is the thread that has two. The two counts are the same pair of edges read
  // from each end, so a model linking a branch to a parent that does not own it
  // answers differently.
  EXPECT_EQ(g_threads_with_a_parent, 2);
  EXPECT_EQ(g_spawned_total, 2);
}

// §37.44 (vpiOrigin -> stmt): a thread's origin is the statement it was
// started from, which it holds apart from its children, so a statement among
// them is no origin.
TEST(ThreadModel, AThreadsOriginIsNoneOfItsChildren) {
  VpiObject frame;
  frame.type = vpiFrame;
  VpiObject stmt;
  stmt.type = vpiBegin;
  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&frame, &stmt};
  EXPECT_EQ(VpiThreadOrigin(&thread), nullptr);
}

// What an application read of the thread a task, called in a fork branch,
// runs in: from inside the task and again once the task has returned.
vpiHandle g_task_frame = nullptr;
vpiHandle g_task_thread = nullptr;
vpiHandle g_thread_frame = nullptr;
vpiHandle g_thread_parent = nullptr;
vpiHandle g_thread_origin = nullptr;
vpiHandle g_parent_origin = nullptr;
bool g_no_frame_after = false;

PLI_INT32 InsideTaskCalltf(PLI_BYTE8*) {
  g_task_frame = vpi_handle(vpiFrame, nullptr);
  g_task_thread = vpi_handle(vpiThread, g_task_frame);
  g_thread_frame = vpi_handle(vpiFrame, g_task_thread);
  g_thread_parent = vpi_handle(vpiParent, g_task_thread);
  g_thread_origin = vpi_handle(vpiOrigin, g_task_thread);
  g_parent_origin = g_thread_parent == nullptr
                        ? nullptr
                        : vpi_handle(vpiOrigin, g_thread_parent);
  return 0;
}

PLI_INT32 AfterTaskCalltf(PLI_BYTE8*) {
  g_no_frame_after = g_task_thread != nullptr &&
                     vpi_handle(vpiFrame, g_task_thread) == nullptr;
  return 0;
}

// §37.44: a fork branch's thread reaches the thread that forked it through
// vpiParent (#7165), the statement it was started from through vpiOrigin, the
// branch's block, as the forking thread reaches the fork (#7166), and through
// vpiFrame the frame active in it now: the task's while the task runs, and
// none once it has returned (§37.43 detail 4) (#7167).
TEST_F(ThreadModelInARun, AForkBranchsThreadReachesItsParentOriginAndFrame) {
  for (const auto& [name, calltf] : {std::pair{"$inside", &InsideTaskCalltf},
                                     std::pair{"$after", &AfterTaskCalltf}}) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic sub; $inside; endtask\n"
      "  initial fork\n"
      "    begin sub(); $after; end\n"
      "  join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NE(g_task_thread, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g_task_thread), vpiThread);
  EXPECT_EQ(g_thread_frame, g_task_frame);
  ASSERT_NE(g_thread_parent, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g_thread_parent), vpiThread);
  ASSERT_NE(g_thread_origin, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g_thread_origin), vpiBegin);
  ASSERT_NE(g_parent_origin, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g_parent_origin), vpiFork);
  EXPECT_TRUE(g_no_frame_after);
}

}  // namespace
}  // namespace delta
