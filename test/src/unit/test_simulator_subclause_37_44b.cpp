#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct ThreadView {
  int origin_type = 0;
  int origin_line = 0;
  bool has_parent = false;
  int parent_line = 0;
  int active = -1;
  std::vector<int> spawned_lines;
  bool spawned_name_it_as_parent = true;
  bool spawned_are_threads = true;
};

struct Snapshot {
  int caller_line = 0;
  std::vector<ThreadView> threads;
};

std::vector<Snapshot> g_snapshots;

int LineOf(vpiHandle obj) {
  return obj == nullptr ? 0 : vpi_get(vpiLineNo, obj);
}

ThreadView ViewOf(vpiHandle thread) {
  ThreadView view;
  vpiHandle origin = vpi_handle(vpiOrigin, thread);
  view.origin_type = origin == nullptr ? 0 : vpi_get(vpiType, origin);
  view.origin_line = LineOf(origin);
  vpiHandle parent = vpi_handle(vpiParent, thread);
  view.has_parent = parent != nullptr;
  if (parent != nullptr) {
    view.parent_line = LineOf(vpi_handle(vpiOrigin, parent));
  }
  view.active = vpi_get(vpiActive, thread);
  vpiHandle it = vpi_iterate(vpiThread, thread);
  if (it == nullptr) return view;
  while (vpiHandle child = vpi_scan(it)) {
    view.spawned_are_threads =
        view.spawned_are_threads && vpi_get(vpiType, child) == vpiThread;
    view.spawned_name_it_as_parent =
        view.spawned_name_it_as_parent &&
        LineOf(vpi_handle(vpiOrigin, vpi_handle(vpiParent, child))) ==
            view.origin_line;
    view.spawned_lines.push_back(LineOf(vpi_handle(vpiOrigin, child)));
  }
  std::ranges::sort(view.spawned_lines);
  return view;
}

PLI_INT32 SnapshotThreadsCalltf(PLI_BYTE8*) {
  Snapshot snapshot;
  snapshot.caller_line = LineOf(vpi_handle(vpiSysTfCall, nullptr));
  vpiHandle it = vpi_iterate(vpiThread, nullptr);
  if (it != nullptr) {
    while (vpiHandle thread = vpi_scan(it)) {
      snapshot.threads.push_back(ViewOf(thread));
    }
  }
  g_snapshots.push_back(snapshot);
  return 0;
}

class ThreadsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_snapshots.clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$threads");
    data.calltf = &SnapshotThreadsCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static const Snapshot& SnapshotFrom(int caller_line) {
    static const Snapshot kNone;
    auto it =
        std::ranges::find(g_snapshots, caller_line, &Snapshot::caller_line);
    EXPECT_NE(it, g_snapshots.end())
        << "no $threads ran on line " << caller_line;
    return it == g_snapshots.end() ? kNone : *it;
  }

  static const ThreadView* ThreadFrom(const Snapshot& snapshot,
                                      int origin_line) {
    auto it = std::ranges::find(snapshot.threads, origin_line,
                                &ThreadView::origin_line);
    return it == snapshot.threads.end() ? nullptr : &*it;
  }
};

struct ProcedureSource {
  const char* name;
  const char* src;
};

class ProceduresAreThreads
    : public ThreadsOfARun,
      public ::testing::WithParamInterface<ProcedureSource> {};

TEST_P(ProceduresAreThreads, AProcedureIsAThreadOfTheRun) {
  Run(GetParam().src);
  const ThreadView* thread = ThreadFrom(SnapshotFrom(3), 3);
  ASSERT_NE(thread, nullptr);
  EXPECT_FALSE(thread->has_parent);
  EXPECT_EQ(thread->active, 1);
}

INSTANTIATE_TEST_SUITE_P(
    EveryKindOfProcedure, ProceduresAreThreads,
    ::testing::Values(
        ProcedureSource{"Initial",
                        "module top;\n"
                        "\n"
                        "  initial $threads;\n"
                        "endmodule\n"},
        ProcedureSource{"Always",
                        "module top; logic go = 0;\n"
                        "  initial #1 go = 1;\n"
                        "  always @(go) $threads;\n"
                        "endmodule\n"},
        ProcedureSource{"AlwaysComb",
                        "module top; logic a = 0, b;\n"
                        "\n"
                        "  always_comb begin b = a; $threads; end\n"
                        "endmodule\n"},
        ProcedureSource{"AlwaysLatch",
                        "module top; logic en = 0, d = 1, q;\n"
                        "  initial #1 en = 1;\n"
                        "  always_latch if (en) begin q = d; $threads; end\n"
                        "endmodule\n"},
        ProcedureSource{"AlwaysFf",
                        "module top; logic clk = 0, q;\n"
                        "  initial #1 clk = 1;\n"
                        "  always_ff @(posedge clk) begin q <= 1; $threads; "
                        "end\n"
                        "endmodule\n"}),
    [](const ::testing::TestParamInfo<ProcedureSource>& info) {
      return std::string(info.param.name);
    });

TEST_F(ThreadsOfARun, AFinalProcedureIsAThreadOfTheRun) {
  Run("module top;\n"
      "\n"
      "  final $threads;\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();
  const ThreadView* thread = ThreadFrom(SnapshotFrom(3), 3);
  ASSERT_NE(thread, nullptr);
  EXPECT_FALSE(thread->has_parent);
  EXPECT_EQ(thread->active, 1);
}

TEST_F(ThreadsOfARun, DISABLED_AnAlwaysProceduresOriginIsItsStatement) {
  Run("module top; logic go = 0;\n"
      "  initial #1 go = 1;\n"
      "  always @(go) $threads;\n"
      "endmodule\n");
  const ThreadView* thread = ThreadFrom(SnapshotFrom(3), 3);
  ASSERT_NE(thread, nullptr);
  EXPECT_EQ(thread->origin_type, vpiEventControl);
}

constexpr const char* kForkOfTwoBranches =
    "module top;\n"
    "  initial\n"
    "    fork\n"
    "      begin #5 $threads; end\n"
    "      begin $threads; #10; end\n"
    "    join\n"
    "endmodule\n";

TEST_F(ThreadsOfARun, AForkingThreadIteratesExactlyItsBranches) {
  Run(kForkOfTwoBranches);
  const ThreadView* forking = ThreadFrom(SnapshotFrom(5), 3);
  ASSERT_NE(forking, nullptr);
  EXPECT_EQ(forking->spawned_lines, (std::vector<int>{4, 5}));
  EXPECT_TRUE(forking->spawned_are_threads);
  EXPECT_TRUE(forking->spawned_name_it_as_parent);
}

TEST_F(ThreadsOfARun, AThreadSpawningNothingIteratesToNone) {
  Run(kForkOfTwoBranches);
  const ThreadView* branch = ThreadFrom(SnapshotFrom(5), 4);
  ASSERT_NE(branch, nullptr);
  EXPECT_TRUE(branch->spawned_lines.empty());
}

TEST_F(ThreadsOfARun, AProceduresThreadHasNoParent) {
  Run(kForkOfTwoBranches);
  const ThreadView* forking = ThreadFrom(SnapshotFrom(5), 3);
  ASSERT_NE(forking, nullptr);
  EXPECT_FALSE(forking->has_parent);
}

TEST_F(ThreadsOfARun, DISABLED_OnlyTheExecutingThreadIsActive) {
  Run(kForkOfTwoBranches);
  const Snapshot& first = SnapshotFrom(5);
  ASSERT_NE(ThreadFrom(first, 3), nullptr);
  ASSERT_NE(ThreadFrom(first, 4), nullptr);
  ASSERT_NE(ThreadFrom(first, 5), nullptr);
  EXPECT_EQ(ThreadFrom(first, 3)->active, 0);
  EXPECT_EQ(ThreadFrom(first, 4)->active, 0);
  EXPECT_EQ(ThreadFrom(first, 5)->active, 1);
}

TEST_F(ThreadsOfARun, DISABLED_TheActiveThreadChangesWhenAnotherRuns) {
  Run(kForkOfTwoBranches);
  const Snapshot& later = SnapshotFrom(4);
  ASSERT_NE(ThreadFrom(later, 4), nullptr);
  ASSERT_NE(ThreadFrom(later, 5), nullptr);
  EXPECT_EQ(ThreadFrom(later, 4)->active, 1);
  EXPECT_EQ(ThreadFrom(later, 5)->active, 0);
}

constexpr const char* kSingleStatementBranches =
    "module top;\n"
    "  task automatic tk(); #2 $threads; endtask\n"
    "  initial fork\n"
    "    #1 $threads;\n"
    "    tk();\n"
    "  join\n"
    "endmodule\n";

TEST_F(ThreadsOfARun, ASingleStatementBranchsOriginIsThatStatement) {
  Run(kSingleStatementBranches);
  const ThreadView* branch = ThreadFrom(SnapshotFrom(4), 4);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(branch->origin_type, vpiDelayControl);
  EXPECT_EQ(branch->parent_line, 3);
}

TEST_F(ThreadsOfARun, ATaskCallBranchsOriginIsTheCall) {
  Run(kSingleStatementBranches);
  const ThreadView* branch = ThreadFrom(SnapshotFrom(2), 5);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(branch->origin_type, vpiTaskCall);
  EXPECT_EQ(branch->parent_line, 3);
}

TEST_F(ThreadsOfARun, ANestedForksBranchHasTheOuterBranchAsParent) {
  Run("module top;\n"
      "  initial fork\n"
      "    begin\n"
      "      fork\n"
      "        begin $threads; end\n"
      "      join\n"
      "    end\n"
      "  join\n"
      "endmodule\n");
  const Snapshot& snapshot = SnapshotFrom(5);
  const ThreadView* inner = ThreadFrom(snapshot, 5);
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->parent_line, 3);
  const ThreadView* outer = ThreadFrom(snapshot, 3);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->parent_line, 2);
  EXPECT_EQ(outer->spawned_lines, std::vector<int>{5});
}

constexpr const char* kForkJoinAny =
    "module top;\n"
    "  initial begin\n"
    "    fork\n"
    "      begin #1; end\n"
    "      begin #5 $threads; end\n"
    "    join_any\n"
    "    #10;\n"
    "  end\n"
    "endmodule\n";

TEST_F(ThreadsOfARun, AJoinAnyForksBranchesAreThreads) {
  Run(kForkJoinAny);
  const ThreadView* branch = ThreadFrom(SnapshotFrom(5), 5);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(branch->parent_line, 2);
}

TEST_F(ThreadsOfARun, AResumedThreadStillIteratesItsRunningJoinAnyBranch) {
  Run(kForkJoinAny);
  const ThreadView* forking = ThreadFrom(SnapshotFrom(5), 2);
  ASSERT_NE(forking, nullptr);
  EXPECT_TRUE(std::ranges::find(forking->spawned_lines, 5) !=
              forking->spawned_lines.end());
}

constexpr const char* kForkJoinNone =
    "module top;\n"
    "  initial begin\n"
    "    fork\n"
    "      begin #5 $threads; end\n"
    "      begin #6; end\n"
    "    join_none\n"
    "    #10;\n"
    "  end\n"
    "endmodule\n";

TEST_F(ThreadsOfARun, AJoinNoneForksBranchesAreThreads) {
  Run(kForkJoinNone);
  const Snapshot& snapshot = SnapshotFrom(4);
  const ThreadView* branch = ThreadFrom(snapshot, 4);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(branch->parent_line, 2);
  EXPECT_NE(ThreadFrom(snapshot, 5), nullptr);
}

TEST_F(ThreadsOfARun, AResumedThreadIteratesItsJoinNoneBranches) {
  Run(kForkJoinNone);
  const ThreadView* forking = ThreadFrom(SnapshotFrom(4), 2);
  ASSERT_NE(forking, nullptr);
  EXPECT_EQ(forking->spawned_lines, (std::vector<int>{4, 5}));
  EXPECT_TRUE(forking->spawned_name_it_as_parent);
}

}  // namespace
}  // namespace delta
