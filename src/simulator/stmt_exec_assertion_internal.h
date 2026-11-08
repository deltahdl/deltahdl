#pragma once

#include <coroutine>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/assert_control_log.h"
#include "simulator/class_object.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

namespace delta {

struct Stmt;

struct PendingReportScope {
  Process* proc = nullptr;
  std::vector<std::string_view> named_scopes;
  ClassObject* this_obj = nullptr;
  const ClassTypeInfo* method_class = nullptr;
  InstancePrefixOverrideState prefix_override;

  static PendingReportScope Capture(SimContext& ctx) {
    return {ctx.CurrentProcess(), ctx.ActiveNamedScopes(), ctx.CurrentThis(),
            ctx.CurrentMethodClass(), ctx.InstancePrefixOverride()};
  }

  bool InClassMethod() const {
    return this_obj != nullptr || method_class != nullptr;
  }

  void Install(SimContext& ctx, PendingReportScope& saved) const {
    saved.proc = ctx.CurrentProcess();
    ctx.SetCurrentProcess(proc);
    saved.named_scopes = ctx.ActiveNamedScopes();
    Replace(ctx, named_scopes);
    saved.this_obj = this_obj;
    saved.method_class = method_class;
    saved.prefix_override = ctx.InstancePrefixOverride();
    ctx.InstancePrefixOverride() = prefix_override;
    if (InClassMethod()) {
      ctx.PushThis(this_obj);
      ctx.PushMethodClass(method_class);
    }
  }

  static void Restore(SimContext& ctx, const PendingReportScope& saved) {
    if (saved.InClassMethod()) {
      ctx.PopMethodClass();
      ctx.PopThis();
    }
    Replace(ctx, saved.named_scopes);
    ctx.InstancePrefixOverride() = saved.prefix_override;
    ctx.SetCurrentProcess(saved.proc);
  }

  static void Replace(SimContext& ctx,
                      const std::vector<std::string_view>& scopes) {
    while (!ctx.ActiveNamedScopes().empty()) ctx.PopActiveNamedScope();
    for (std::string_view scope : scopes) ctx.PushActiveNamedScope(scope);
  }
};

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

Process* CreateAssertionChildProcess(SimContext& ctx, Arena& arena,
                                     Region home_region);

void ScheduleAssertionChildStart(Process* p, Region region, SimContext& ctx);

void ExecConcurrentAssertionTick(const Stmt* stmt,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena);

void AbortKilledAttempts(const AssertControlCall& call, SimContext& ctx);

void AbortAttemptStartedAt(std::string_view key, uint64_t started,
                           SimContext& ctx);

AssertionStatus AssertionControlStatus(const Stmt* stmt, SimContext& ctx);

}  // namespace delta
