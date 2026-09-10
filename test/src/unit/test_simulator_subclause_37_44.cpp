#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

// vpiOrigin -> stmt: a thread reaches its originating statement, and reports
// none when no origin statement is attached or the handle is null.
TEST(ThreadModel, OriginRelationReachesTheOriginatingStatement) {
  VpiObject origin;
  origin.type = vpiStmt;

  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&origin};
  EXPECT_EQ(VpiThreadOrigin(&thread), &origin);

  VpiObject bare;
  bare.type = vpiThread;
  EXPECT_EQ(VpiThreadOrigin(&bare), nullptr);
  EXPECT_EQ(VpiThreadOrigin(nullptr), nullptr);
}

// frame -- thread (detail 1): a thread reaches its active frame. Only the frame
// child is reported, even when other children (here the origin statement) are
// present alongside it.
TEST(ThreadModel, FrameRelationReachesTheActiveFrame) {
  VpiObject origin;
  origin.type = vpiStmt;
  VpiObject frame;
  frame.type = vpiFrame;

  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&origin, &frame};
  EXPECT_EQ(VpiThreadFrame(&thread), &frame);

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
// §37.44 detail 1: "A thread is a SystemVerilog process such as an always
// procedure or a branch of a fork construct." Every case above builds its
// threads by hand, which says what the model reports about an object and
// nothing about where such an object comes from -- and no run produced one at
// all, so the whole of this model answered for a design only in a test that
// wrote the design's threads itself.
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

int InspectThreadsCalltf(const char*) {
  vpiHandle threads = vpi_iterate(vpiThread, nullptr);
  if (threads == nullptr) return 0;
  for (vpiHandle t = vpi_scan(threads); t != nullptr; t = vpi_scan(threads)) {
    ++g_threads_seen;
    if (vpi_get(vpiType, t) != vpiThread) ++g_non_threads_seen;
    if (VpiThreadParent(t) != nullptr) ++g_threads_with_a_parent;
    g_spawned_total += static_cast<int>(VpiThreadThreads(t).size());
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
  data.tfname = "$probe";
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

}  // namespace
}  // namespace delta
