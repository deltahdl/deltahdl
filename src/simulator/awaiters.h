#pragma once

#include <algorithm>
#include <coroutine>
#include <cstdint>
#include <functional>
#include <limits>
#include <memory>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

struct DelayAwaiter {
  SimContext& ctx;
  uint64_t delay_ticks;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    if (delay_ticks >
        std::numeric_limits<uint64_t>::max() - ctx.CurrentTime().ticks) {
      return;
    }
    auto time = ctx.CurrentTime() + SimTime{delay_ticks};
    auto region = SelectDelayRegion();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto* proc = ctx.CurrentProcess();
    event->callback = [h, proc, &ctx = ctx]() mutable {
      if (proc && !proc->active) return;

      if (proc && proc->is_suspended) {
        proc->pending_wake = h;
        return;
      }
      if (proc) ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(time, region, event);
  }

  Region SelectDelayRegion() const {
    if (delay_ticks != 0) {
      return ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
    }
    return ctx.IsReactiveContext() ? Region::kReInactive : Region::kInactive;
  }

  void await_resume() const noexcept {}
};

struct NamedEventAwaiter {
  SimContext& ctx;
  std::string_view event_name;
  Variable* event = nullptr;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* var = event != nullptr ? event : ctx.FindVariable(event_name);
    if (!var) return;
    auto* proc = ctx.CurrentProcess();
    if (proc) proc->waiting_on_events.assign(1, var);
    auto* ctx_ptr = &ctx;
    var->AddWatcher([h, proc, ctx_ptr]() mutable {
      if (proc && proc->is_suspended) return false;
      auto* saved = ctx_ptr->CurrentProcess();
      if (proc) ctx_ptr->SetCurrentProcess(proc);
      h.resume();
      ctx_ptr->SetCurrentProcess(saved);
      return true;
    });
  }

  void await_resume() const noexcept {
    if (Process* proc = ctx.CurrentProcess()) proc->waiting_on_events.clear();
  }
};

inline bool NamesStaticProperty(SimContext& ctx, std::string_view name) {
  auto scope = name.rfind("::");
  if (scope == std::string_view::npos) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(name.substr(0, scope));
  return cls != nullptr &&
         cls->StaticPropertyDeclarer(name.substr(scope + 2)) != nullptr;
}

inline void DropUnwatchableNames(SimContext& ctx,
                                 std::vector<std::string_view>& names) {
  auto designates_no_object = [&ctx](std::string_view name) {
    return ctx.FindVariable(name) == nullptr && !NamesStaticProperty(ctx, name);
  };
  names.erase(std::remove_if(names.begin(), names.end(), designates_no_object),
              names.end());
}

struct AnyChangeAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& var_names;
  std::shared_ptr<bool> finished = nullptr;
  bool strength_changes = false;

  bool await_ready() const noexcept { return false; }

  struct WatchedObject {
    Variable* var;
    bool value_backed;
    bool strength_changes;
  };

  struct ObservedState {
    Logic4Snapshot bits;
    uint64_t triggered_ticks = UINT64_MAX;
    uint64_t strength_generation = 0;

    void Capture(const Variable& var) {
      bits.Capture(var.value);
      triggered_ticks = var.triggered_ticks;
      strength_generation = var.strength_generation;
    }
  };

  static bool StateLivesInValue(SimContext& ctx, const Variable& var,
                                std::string_view name) {
    if (var.is_event) return false;
    return ctx.FindQueue(name) == nullptr &&
           ctx.FindAssocArray(name) == nullptr &&
           ctx.GetVariableClassType(name).empty();
  }

  static bool ChangeGatePasses(const WatchedObject& watched,
                               ObservedState& prev, uint64_t now_ticks) {
    if (!watched.value_backed) return true;
    const Variable& var = *watched.var;
    bool moved =
        var.triggered_ticks != prev.triggered_ticks ||
        !EventAwaiter::Logic4VecBitsEqual(prev.bits.Get(), var.value) ||
        (watched.strength_changes &&
         var.strength_generation != prev.strength_generation);
    bool triggered_now = var.triggered_ticks == now_ticks;
    prev.Capture(var);
    return moved || triggered_now;
  }

  static bool KeepWakeWhileSuspended(Process* proc, std::coroutine_handle<> h) {
    if (proc == nullptr || !proc->is_suspended) return false;
    proc->pending_wake = h;
    return true;
  }

  void AttachChangeWatcher(WatchedObject watched, std::coroutine_handle<> h,
                           Process* proc, const std::shared_ptr<bool>& fin,
                           const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &ctx;
    Variable* var = watched.var;
    var->prev_value.Capture(var->value);
    ObservedState prev;
    prev.Capture(*var);
    var->AddWatcher([h, watched, prev, proc, ctx_ptr, fin, consumed]() mutable {
      if (fin) {
        if (*fin) return true;
      } else if (h.done()) {
        return true;
      }
      if (proc && !proc->active) return true;
      if (*consumed) return true;
      if (!ChangeGatePasses(watched, prev, ctx_ptr->CurrentTime().ticks))
        return false;
      *consumed = true;
      if (KeepWakeWhileSuspended(proc, h)) return true;
      EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    });
  }

  void AttachOwnPropertyWatcher(std::string_view name,
                                std::coroutine_handle<> h, Process* proc,
                                const std::shared_ptr<bool>& fin,
                                const std::shared_ptr<bool>& consumed) {
    auto* self = ctx.CurrentThis();
    if (self == nullptr || self->type == nullptr) return;
    if (name != "this" && self->type->FindProperty(name) == nullptr) return;
    self->AddWatcher(WakeOnceWatcher(h, proc, fin, consumed));
  }

  bool AttachStaticPropertyWatcher(std::string_view name,
                                   std::coroutine_handle<> h, Process* proc,
                                   const std::shared_ptr<bool>& fin,
                                   const std::shared_ptr<bool>& consumed) {
    const ClassTypeInfo* cls = ctx.CurrentMethodClass();
    std::string_view member = name;
    auto scope = name.rfind("::");
    if (scope != std::string_view::npos) {
      cls = ctx.FindClassType(name.substr(0, scope));
      member = name.substr(scope + 2);
    }
    if (cls == nullptr) return false;
    cls = cls->StaticPropertyDeclarer(member);
    if (cls == nullptr) return false;
    cls->AddStaticWatcher(WakeOnceWatcher(h, proc, fin, consumed));
    return true;
  }

  std::function<bool()> WakeOnceWatcher(std::coroutine_handle<> h,
                                        Process* proc,
                                        const std::shared_ptr<bool>& fin,
                                        const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &ctx;
    return [h, proc, ctx_ptr, fin, consumed]() mutable {
      if (fin) {
        if (*fin) return true;
      } else if (h.done()) {
        return true;
      }
      if (proc && !proc->active) return true;
      if (*consumed) return true;
      *consumed = true;
      EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    };
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto fin = finished;
    auto consumed = std::make_shared<bool>(false);
    for (auto name : var_names) {
      auto* var =
          NameDenotesVariable(name, ctx) ? ctx.FindVariable(name) : nullptr;
      if (!var) {
        if (!AttachStaticPropertyWatcher(name, h, proc, fin, consumed))
          AttachOwnPropertyWatcher(name, h, proc, fin, consumed);
        continue;
      }
      AttachChangeWatcher(
          {var, StateLivesInValue(ctx, *var, name), strength_changes}, h, proc,
          fin, consumed);
    }
  }

  void await_resume() const noexcept {}
};

struct InertialDelayAwaiter {
  SimContext& ctx;
  uint64_t delay_ticks;
  const std::vector<std::string_view>& var_names;
  std::shared_ptr<bool> fired = std::make_shared<bool>(false);
  std::shared_ptr<bool> expired = std::make_shared<bool>(false);

  bool await_ready() const noexcept { return false; }

  void ScheduleTimeoutEvent(std::coroutine_handle<> h, Process* proc) {
    auto time = ctx.CurrentTime() + SimTime{delay_ticks};
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto f = fired;
    auto e = expired;
    event->superseded = f;
    event->callback = [h, proc, f, e, &ctx = ctx]() mutable {
      if (*f) return;
      *f = true;
      *e = true;
      if (proc && !proc->active) return;
      if (proc) ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(time, Region::kActive, event);
  }

  void ArmCancelWatchers(std::coroutine_handle<> h, Process* proc) {
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value.Capture(var->value);
      auto f2 = fired;
      var->AddWatcher([h, proc, f2, &ctx = ctx]() mutable {
        if (*f2) return true;
        *f2 = true;
        if (proc && !proc->active) return true;
        auto* writer = ctx.CurrentProcess();
        if (proc) ctx.SetCurrentProcess(proc);
        h.resume();
        ctx.SetCurrentProcess(writer);
        return true;
      });
    }
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    ScheduleTimeoutEvent(h, proc);
    ArmCancelWatchers(h, proc);
  }

  bool await_resume() const noexcept { return *expired; }
};

struct ForkJoinState {
  uint32_t remaining = 0;
  std::coroutine_handle<> parent;
  Process* parent_proc = nullptr;
  bool join_any = false;
  bool resumed = false;
};

struct ForkJoinAwaiter {
  ForkJoinState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->parent = h; }

  void await_resume() const noexcept {}
};

struct WaitForkAwaiter {
  WaitForkState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->waiter = h; }

  void await_resume() const noexcept {}
};

struct CycleDelayAwaiter {
  SimContext& ctx;
  uint32_t cycles;

  bool await_ready() const noexcept {
    if (cycles != 0) return false;
    auto* mgr = ctx.GetClockingManager();
    if (!mgr) return true;
    auto block_name = mgr->DefaultClockingFor(ctx);
    if (block_name.empty()) return true;
    return mgr->ZeroCycleDelayProceeds(block_name, ctx.CurrentTime());
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* mgr = ctx.GetClockingManager();
    if (!mgr) {
      h.resume();
      return;
    }
    auto block_name = mgr->DefaultClockingFor(ctx);
    if (block_name.empty()) {
      h.resume();
      return;
    }
    auto* proc = ctx.CurrentProcess();
    if (cycles == 0) {
      mgr->RegisterEdgeWait(block_name, [h, proc, &ctx = ctx]() {
        ResumeIn(h, proc, ctx);
        return false;
      });
      return;
    }
    SimTime start = ctx.CurrentTime();
    mgr->RegisterEdgeWait(
        block_name, [h, proc, start, remaining = cycles, &ctx = ctx]() mutable {
          if (ctx.CurrentTime() == start) return true;
          if (--remaining > 0) return true;
          ResumeIn(h, proc, ctx);
          return false;
        });
  }

  static void ResumeIn(std::coroutine_handle<> h, Process* proc,
                       SimContext& ctx) {
    if (proc && !proc->active) return;
    if (proc && proc->is_suspended) {
      proc->pending_wake = h;
      return;
    }
    if (proc) ctx.SetCurrentProcess(proc);
    h.resume();
  }

  void await_resume() const noexcept {}
};

struct ProcessAwaitAwaiter {
  Process* target;

  bool await_ready() {
    return !target || target->sv_state == ProcessState::kFinished ||
           target->sv_state == ProcessState::kKilled;
  }

  void await_suspend(std::coroutine_handle<> h) {
    target->await_waiters.push_back(h);
  }

  void await_resume() const noexcept {}
};

inline std::function<void()> SyncWaiterResume(std::coroutine_handle<> h,
                                              SimContext* ctx,
                                              const void* object) {
  if (ctx == nullptr) return h;
  Process* proc = ctx->CurrentProcess();
  if (proc != nullptr) proc->waiting_on_sync = object;
  return [h, proc, ctx] {
    if (proc != nullptr) proc->waiting_on_sync = nullptr;
    Process* waker = ctx->CurrentProcess();
    CycleDelayAwaiter::ResumeIn(h, proc, *ctx);
    ctx->SetCurrentProcess(waker);
  };
}

struct SemaphoreGetAwaiter {
  SemaphoreObject& sem;
  int32_t count;
  SimContext* ctx = nullptr;

  bool await_ready() {
    auto status = sem.Get(count);
    return status != SemGetStatus::kBlock;
  }

  void await_suspend(std::coroutine_handle<> h) {
    sem.waiters.emplace_back(count, SyncWaiterResume(h, ctx, &sem));
  }

  void await_resume() const noexcept {}
};

struct MailboxPutAwaiter {
  MailboxObject& mbx;
  Logic4Snapshot msg;
  MailboxMessageType type;
  bool placed = false;
  SimContext* ctx = nullptr;

  bool await_ready() {
    placed = mbx.Put(msg.Get(), type) == MbxPutStatus::kPlaced;
    return placed;
  }

  void await_suspend(std::coroutine_handle<> h) {
    mbx.put_waiters.push_back(SyncWaiterResume(h, ctx, &mbx));
  }

  void await_resume() {
    if (!placed) mbx.Put(msg.Get(), type);
  }
};

struct MailboxGetAwaiter {
  MailboxObject& mbx;
  MailboxMessageType expected;
  Logic4Snapshot msg;
  MbxGetStatus status = MbxGetStatus::kBlock;
  SimContext* ctx = nullptr;

  bool await_ready() {
    status = mbx.Get(msg, expected);
    return status != MbxGetStatus::kBlock;
  }

  void await_suspend(std::coroutine_handle<> h) {
    mbx.get_waiters.push_back(SyncWaiterResume(h, ctx, &mbx));
  }

  MbxGetStatus await_resume() {
    if (status == MbxGetStatus::kBlock) status = mbx.Get(msg, expected);
    return status;
  }
};

struct MailboxPeekAwaiter {
  MailboxObject& mbx;
  MailboxMessageType expected;
  Logic4Snapshot msg;
  MbxPeekStatus status = MbxPeekStatus::kBlock;
  SimContext* ctx = nullptr;

  bool await_ready() {
    status = mbx.Peek(msg, expected);
    return status != MbxPeekStatus::kBlock;
  }

  void await_suspend(std::coroutine_handle<> h) {
    mbx.peek_waiters.push_back(SyncWaiterResume(h, ctx, &mbx));
  }

  MbxPeekStatus await_resume() {
    if (status == MbxPeekStatus::kBlock) status = mbx.Peek(msg, expected);
    return status;
  }
};

}  // namespace delta
