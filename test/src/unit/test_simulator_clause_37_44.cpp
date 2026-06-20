#include <gtest/gtest.h>

#include <vector>

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

}  // namespace
}  // namespace delta
