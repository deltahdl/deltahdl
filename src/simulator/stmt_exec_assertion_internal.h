#pragma once

#include <coroutine>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

namespace delta {

struct Stmt;

// What the concurrent assertion executor in stmt_exec_deferred.cpp shares
// with the procedural assertion queue of procedural_assertion.cpp: the
// scope a report stands in, the processes an assertion creates beside the
// one reaching it, and one tick of a statement's property.

// §16.4.1: a pending assertion report is placed in the queue of the process
// executing the assertion, and §20.10 has its severity message and §21.2.1.5
// its %m name the hierarchical scope of the statement, which the labels the
// process stands inside are part of. The report's event runs after the process
// has moved on or suspended, with the context holding whatever ran last, so
// the process and its named scopes are recorded when the report is queued and
// stood back up around the report, then put back as they were.
struct PendingReportScope {
  Process* proc = nullptr;
  std::vector<std::string_view> named_scopes;

  static PendingReportScope Capture(const SimContext& ctx) {
    return {ctx.CurrentProcess(), ctx.ActiveNamedScopes()};
  }

  // Stands the captured scopes up in the captured process's place, keeping
  // in `saved` what Restore puts back: the process that was current, and
  // the captured process's own scopes, which the switch brought in with it
  // and which it keeps, the report's standing in their place only until
  // the report is done.
  void Install(SimContext& ctx, PendingReportScope& saved) const {
    saved.proc = ctx.CurrentProcess();
    ctx.SetCurrentProcess(proc);
    saved.named_scopes = ctx.ActiveNamedScopes();
    Replace(ctx, named_scopes);
  }

  static void Restore(SimContext& ctx, const PendingReportScope& saved) {
    Replace(ctx, saved.named_scopes);
    ctx.SetCurrentProcess(saved.proc);
  }

  static void Replace(SimContext& ctx,
                      const std::vector<std::string_view>& scopes) {
    while (!ctx.ActiveNamedScopes().empty()) ctx.PopActiveNamedScope();
    for (std::string_view scope : scopes) ctx.PushActiveNamedScope(scope);
  }
};

// §16.5: "Concurrent assertions ... are evaluated in the Observed region", and
// §16.14.6 has one embedded in procedural code "evaluated as though it were a
// separate concurrent assertion", so where the statement is written does not
// change the region its property is evaluated in. A module-item concurrent
// assertion is carried by a process the scheduler already resumes there
// (Process::is_concurrent_clocked, see ResumeMaybeReactive in
// simulator/awaiters_event_control.h); one written inside a procedure is
// reached in whatever region that procedure is running in, which for an
// `always @(posedge clk)` is the Active region -- in the middle of the write
// that assigned the clock.
//
// A procedural statement's instance is placed in the queue of
// procedural_assertion.cpp, whose monitor process wakes at the statement's
// leading clocking event and suspends into the Observed region through this;
// a process the lowerer started no monitor for, one a fork spawned, suspends
// its own procedure into the region instead and resumes the statements after
// the assertion with it, which §4.4.2.2's keeping ordinary procedural code in
// the Active region makes the cost of that path.
//
// §16.17 has the statement following an expect scheduled after the Observed
// region in which its property completed, so the same awaiter carries a
// process into the Reactive region, where §4.4.2.6 puts a concurrent
// assertion's action block as well.
struct RegionAwaiter {
  SimContext& ctx;
  Region region = Region::kObserved;

  bool await_ready() const noexcept {
    return ctx.GetScheduler().CurrentRegion() == region;
  }

  void await_suspend(std::coroutine_handle<> h) const {
    auto* proc = ctx.CurrentProcess();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto* ctx_ptr = &ctx;
    event->callback = [h, proc, ctx_ptr]() mutable {
      if (proc != nullptr && !proc->active) return;
      if (proc != nullptr) ctx_ptr->SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, event);
  }

  void await_resume() const noexcept {}
};

// A process created by an assertion beside the one reaching it, an action
// block's or an attempt's, in `home_region`, standing in the asserting
// process's instance and named scopes with a random seed drawn from it.
Process* CreateAssertionChildProcess(SimContext& ctx, Arena& arena,
                                     Region home_region);

// Starts the process at the current time in `region`, where its coroutine
// runs to its first wait. A process disabled before that is left where it
// is.
void ScheduleAssertionChildStart(Process* p, Region region, SimContext& ctx);

// One tick of the leading clock of the concurrent assertion `stmt` carries,
// in the current process, whose state the attempts in flight are kept on:
// every attempt in flight advances and one new one begins per entry of
// `instances`, a null entry for a static assertion's and, §16.14.6.1, the
// values a matured instance of a procedural one saved, the verdicts reached
// at the tick concluding the assertion, its action block scheduled into the
// Reactive region. Called in the Observed region of the tick.
void ExecConcurrentAssertionTick(const Stmt* stmt,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena);

}  // namespace delta
