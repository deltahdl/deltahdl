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

TEST(ThreadModel, ParentRelationReachesTheSpawningThread) {
  VpiObject parent;
  parent.type = vpiThread;

  VpiObject child;
  child.type = vpiThread;
  child.parent = &parent;

  EXPECT_EQ(VpiThreadParent(&child), &parent);
}

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

TEST(ThreadModel, FrameRelationReachesTheActiveFrame) {
  VpiObject inner;
  inner.type = vpiFrame;
  VpiObject outer;
  outer.type = vpiFrame;
  outer.active = true;
  outer.children = {&inner};

  VpiObject spawned;
  spawned.type = vpiThread;
  spawned.active = true;
  VpiObject thread;
  thread.type = vpiThread;
  thread.children = {&outer, &spawned};
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

TEST(ThreadModel, AnotherRelationIsNotTheThreadsToResolve) {
  VpiObject thread;
  thread.type = vpiThread;
  VpiObject before;
  VpiHandle out = &before;
  EXPECT_FALSE(VpiTryResolveThreadRelation(vpiStmt, &thread, out));
  EXPECT_EQ(out, &before);
}

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

TEST(ThreadModel, ThreadIterationIsEmptyWhenNoneSpawned) {
  VpiObject thread;
  thread.type = vpiThread;
  EXPECT_TRUE(VpiThreadThreads(&thread).empty());
  EXPECT_TRUE(VpiThreadThreads(nullptr).empty());
}

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

  EXPECT_GE(g_threads_seen, 3);
  EXPECT_EQ(g_non_threads_seen, 0);
}

TEST_F(ThreadModelInARun, AForkBranchReachesTheThreadThatSpawnedIt) {
  RegisterThreadProbe();

  SimFixture f;
  RunAForkOfTwoBranches(f);

  EXPECT_EQ(g_threads_with_a_parent, 2);
  EXPECT_EQ(g_spawned_total, 2);
}

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
