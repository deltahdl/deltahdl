// §non-lrm:scheduler

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"
#include "simulation/compiled_sim.h"
#include "simulation/mt_sim.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- EventPool tests ---
TEST(EventPool, AcquireCreatesNew) {
  Arena arena;
  EventPool pool(arena);
  Event* ev = pool.Acquire();
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(ev->kind, EventKind::kEvaluation);
  EXPECT_EQ(ev->target, nullptr);
  EXPECT_EQ(ev->next, nullptr);
}

TEST(EventPool, FreeCount) {
  Arena arena;
  EventPool pool(arena);
  EXPECT_EQ(pool.FreeCount(), 0);

  Event* ev1 = pool.Acquire();
  Event* ev2 = pool.Acquire();
  pool.Release(ev1);
  pool.Release(ev2);
  EXPECT_EQ(pool.FreeCount(), 2);

  pool.Acquire();
  EXPECT_EQ(pool.FreeCount(), 1);
}

TEST(Scheduler, EventPoolIntegration) {
  Arena arena;
  Scheduler sched(arena);
  auto& pool = sched.GetEventPool();
  EXPECT_EQ(pool.FreeCount(), 0);

  auto* ev = pool.Acquire();
  bool ran = false;
  ev->callback = [&ran]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_TRUE(ran);
  // After execution, event should be recycled into the pool.
  EXPECT_EQ(pool.FreeCount(), 1);
}

TEST(Process, MoveSemantics) {
  SimCoroutine a = MakeTestCoroutine();
  EXPECT_FALSE(a.Done());

  SimCoroutine* pa = &a;
  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.Done());
  EXPECT_TRUE(pa->Done());  // Moved-from state check via pre-move pointer.
}

TEST(Process, ProcessIdAssignment) {
  Process p1;
  p1.id = 42;
  Process p2;
  p2.id = 43;
  EXPECT_NE(p1.id, p2.id);
}

TEST(Process, CoroutineRelease) {
  SimCoroutine coro = MakeTestCoroutine();
  auto handle = coro.Release();
  EXPECT_TRUE(coro.Done());
  EXPECT_NE(handle, nullptr);
  // Clean up the released handle.
  handle.destroy();
}

TEST(EventPool, ReleaseAndReuse) {
  Arena arena;
  EventPool pool(arena);
  Event* ev = pool.Acquire();
  ev->callback = []() {};
  ev->target = reinterpret_cast<void*>(0x1234);
  pool.Release(ev);
  EXPECT_EQ(pool.FreeCount(), 1);

  Event* reused = pool.Acquire();
  EXPECT_EQ(reused, ev);               // Same pointer returned
  EXPECT_EQ(reused->target, nullptr);  // Fields cleared
  EXPECT_EQ(pool.FreeCount(), 0);
}

// =============================================================================
// EventCoalescer
// =============================================================================
TEST(AdvSim, EventCoalescerMergesDuplicates) {
  EventCoalescer coalescer;
  uint32_t target_id = 42;
  coalescer.Add(target_id, 100);
  coalescer.Add(target_id, 200);
  coalescer.Add(target_id, 300);
  // Only last value for each target should survive.
  auto entries = coalescer.Drain();
  ASSERT_EQ(entries.size(), 1u);
  EXPECT_EQ(entries[0].target_id, target_id);
  EXPECT_EQ(entries[0].value, 300u);
}

TEST(AdvSim, EventCoalescerDrainClearsState) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  auto first = coalescer.Drain();
  EXPECT_EQ(first.size(), 1u);
  auto second = coalescer.Drain();
  EXPECT_TRUE(second.empty());
}

// =============================================================================
// Partitioner
// =============================================================================
TEST(MtSim, IndependentProcessesSinglePartition) {
  Partitioner part;
  // Process 0 reads "a", writes "b".
  part.AddDependency({0, {"a"}, {"b"}});
  // Process 1 reads "c", writes "d".
  part.AddDependency({1, {"c"}, {"d"}});

  auto partitions = part.BuildPartitions();
  // No conflicts: both should end up in the same partition.
  EXPECT_EQ(partitions.size(), 1u);
  EXPECT_EQ(partitions[0].process_ids.size(), 2u);
}

TEST(MtSim, ConflictingProcessesSeparatePartitions) {
  Partitioner part;
  // Process 0 writes "x".
  part.AddDependency({0, {}, {"x"}});
  // Process 1 reads "x".
  part.AddDependency({1, {"x"}, {}});

  auto partitions = part.BuildPartitions();
  // Write-read conflict: must be in separate partitions.
  EXPECT_EQ(partitions.size(), 2u);
}

TEST(MtSim, WriteWriteConflict) {
  Partitioner part;
  part.AddDependency({0, {}, {"sig"}});
  part.AddDependency({1, {}, {"sig"}});

  auto partitions = part.BuildPartitions();
  EXPECT_EQ(partitions.size(), 2u);
}

TEST(MtSim, EmptyPartitioner) {
  Partitioner part;
  auto partitions = part.BuildPartitions();
  EXPECT_TRUE(partitions.empty());
  EXPECT_EQ(part.ProcessCount(), 0u);
}

// =============================================================================
// MtScheduler
// =============================================================================
TEST(MtSim, MtSchedulerInit) {
  MtScheduler sched(4);
  EXPECT_EQ(sched.NumThreads(), 4u);
  EXPECT_EQ(sched.NumPartitions(), 0u);
}

TEST(MtSim, MtSchedulerSetPartitions) {
  MtScheduler sched(2);
  std::vector<SimPartition> parts;
  parts.push_back({0, {0, 1}});
  parts.push_back({1, {2, 3}});
  sched.SetPartitions(parts);

  EXPECT_EQ(sched.NumPartitions(), 2u);
  EXPECT_EQ(sched.Partitions()[0].process_ids.size(), 2u);
  EXPECT_EQ(sched.Partitions()[1].process_ids.size(), 2u);
}

TEST(MtSim, RunTimestepExecutesProcesses) {
  MtSimFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* b = f.ctx.CreateVariable("b", 32);
  b->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Two compiled processes: proc0 sets a=42, proc1 sets b=99.
  std::vector<CompiledProcess> processes;
  processes.emplace_back(0, [](SimContext& ctx) {
    auto* var = ctx.FindVariable("a");
    if (var) var->value.words[0].aval = 42;
  });
  processes.emplace_back(1, [](SimContext& ctx) {
    auto* var = ctx.FindVariable("b");
    if (var) var->value.words[0].aval = 99;
  });

  // Two independent partitions.
  std::vector<SimPartition> partitions = {{0, {0}}, {1, {1}}};

  MtScheduler sched(2);
  sched.SetPartitions(partitions);
  sched.RunTimestep(f.ctx, processes);

  EXPECT_EQ(a->value.ToUint64(), 42u);
  EXPECT_EQ(b->value.ToUint64(), 99u);
}

TEST(MtSim, RunTimestepEmptyPartitions) {
  MtSimFixture f;
  std::vector<CompiledProcess> processes;
  MtScheduler sched(2);
  sched.RunTimestep(f.ctx, processes);
  // Should not crash.
}

TEST(MtSim, RunTimestepMultipleThreads) {
  MtSimFixture f;

  // Use string literals for stable string_view keys.
  const char* names[] = {"v0", "v1", "v2", "v3"};
  std::vector<Variable*> vars;
  for (int i = 0; i < 4; ++i) {
    auto* var = f.ctx.CreateVariable(names[i], 32);
    var->value = MakeLogic4VecVal(f.arena, 32, 0);
    vars.push_back(var);
  }

  // 4 processes, each incrementing a separate variable.
  std::vector<CompiledProcess> processes;
  processes.reserve(4);
  for (uint32_t i = 0; i < 4; ++i) {
    processes.emplace_back(i, [i, &names](SimContext& ctx) {
      auto* var = ctx.FindVariable(names[i]);
      if (var) var->value.words[0].aval += 1;
    });
  }

  // 4 independent partitions.
  std::vector<SimPartition> partitions;
  partitions.reserve(4);
  for (uint32_t i = 0; i < 4; ++i) {
    partitions.push_back({i, {i}});
  }

  MtScheduler sched(4);
  sched.SetPartitions(partitions);
  sched.RunTimestep(f.ctx, processes);

  for (int i = 0; i < 4; ++i) {
    EXPECT_EQ(vars[i]->value.ToUint64(), 1u) << "Variable " << names[i];
  }
}

TEST(Process, ProcessResumeNullSafe) {
  Process p;
  p.Resume();
  EXPECT_TRUE(p.Done());
}

TEST(Process, CoroutineDestroyOnScopeExit) {
  SimCoroutine coro = MakeTestCoroutine();
  // Immediately destroyed — no leak if sanitizer passes.
}

// Helper: lex a single token from source text.
// Returns both the SourceManager (owning the source buffer) and the token
// so that token.text (a string_view) remains valid.
// Helper: parse source and return the compilation unit.
struct ParseResult314 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult314 Parse(const std::string& src) {
  ParseResult314 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// 9. SimTime: simulation time is maintained as ticks with comparison
// and addition operators.
TEST(ParserClause03, Cl3_14_SimTimeOperations) {
  SimTime t0{0};
  SimTime t1{1000};
  SimTime t2{1000};
  EXPECT_EQ(t0.ticks, 0u);
  EXPECT_EQ(t1.ticks, 1000u);
  EXPECT_TRUE(t0 < t1);
  EXPECT_TRUE(t0 <= t1);
  EXPECT_FALSE(t0 > t1);
  EXPECT_TRUE(t1 > t0);
  EXPECT_TRUE(t1 == t2);
  SimTime t3 = t0 + t1;
  EXPECT_EQ(t3.ticks, 1000u);
}

}  // namespace
