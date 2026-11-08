#pragma once

#include <coroutine>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_event_property.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_always_comb.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

struct EdgeSpec {
  Edge edge;
  const Expr* iff_cond;
};

struct ResumeTarget {
  SimContext& ctx;
  Process* proc;
  bool after_observed = false;
};

struct MemberOperand {
  uint64_t handle;
  std::string_view member;
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
};

struct StaticPropertyOperand {
  const ClassTypeInfo* cls;
  std::string_view member;
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
};

struct CompoundOperand {
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
  const Expr* signal;
};

inline std::string_view MemberAccessField(const Expr* signal) {
  if (signal->rhs && signal->rhs->kind == ExprKind::kIdentifier)
    return signal->rhs->text;
  return signal->text;
}

inline bool CollectVirtualInterfaceMember(const Expr* signal, SimContext& ctx,
                                          std::string& name) {
  if (signal->is_scope_resolution) return false;
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(signal->lhs, ctx, ctx.GetArena());
  if (!base.is_virtual_interface) return false;
  name = VirtualInterfaceComponentName(base.handle, MemberAccessField(signal),
                                       ctx);
  return true;
}

inline bool ResolveVirtualInterfaceSignal(const Expr* signal, SimContext& ctx,
                                          Variable** out) {
  *out = nullptr;
  std::string target;
  if (!CollectVirtualInterfaceMember(signal, ctx, target)) return false;
  if (target.empty()) {
    ReportNullVirtualInterface(signal->range.start, ctx);
    return true;
  }
  *out = ctx.FindVariable(target);
  return true;
}

inline Variable* ResolveMemberAccessSignal(const Expr* signal,
                                           SimContext& ctx) {
  Variable* var = nullptr;
  auto* mgr = ctx.GetClockingManager();
  std::string_view member = MemberAccessField(signal);
  if (mgr && !member.empty() && signal->lhs != nullptr) {
    if (const ClockingBlock* block = ResolveClockingBlockOf(signal->lhs, ctx))
      var = mgr->ClockvarVariable(*block, member, ctx);
  }
  if (!var && ResolveVirtualInterfaceSignal(signal, ctx, &var)) return var;
  if (!var) {
    std::string hier_name;
    BuildLhsName(signal, hier_name);
    var = ctx.FindVariable(hier_name);
  }
  return var;
}

inline Variable* ResolveSignalToVariable(const Expr* signal, SimContext& ctx) {
  if (signal->kind == ExprKind::kIdentifier) {
    if (signal->scope_prefix == "$root") {
      std::string rooted_name;
      BuildLhsName(signal, rooted_name);
      return ctx.FindVariable(rooted_name);
    }
    return ctx.FindVariable(signal->text);
  }
  if (signal->kind == ExprKind::kMemberAccess) {
    return ResolveMemberAccessSignal(signal, ctx);
  }
  return nullptr;
}

inline bool DenotesAClassObject(const Expr* base, SimContext& ctx) {
  if (base == nullptr) return false;
  if (base->kind == ExprKind::kIdentifier) {
    if (base->text == "this" || base->text == "super")
      return ctx.CurrentThis() != nullptr;
    if (!ctx.GetVariableClassType(base->text).empty()) return true;
    auto* self = ctx.CurrentThis();
    return self != nullptr && self->type != nullptr &&
           self->type->FindProperty(base->text) != nullptr;
  }
  return base->kind == ExprKind::kMemberAccess && !base->is_scope_resolution &&
         DenotesAClassObject(base->lhs, ctx);
}

inline uint64_t ResolveMemberObjectHandle(const Expr* signal, SimContext& ctx,
                                          std::string_view& member) {
  const ClassObject* obj = nullptr;
  if (signal->kind == ExprKind::kIdentifier) {
    member = signal->text;
    obj = ctx.CurrentThis();
  } else if (signal->kind == ExprKind::kMemberAccess &&
             !signal->is_scope_resolution &&
             DenotesAClassObject(signal->lhs, ctx)) {
    member = MemberAccessField(signal);
    Logic4Vec base = EvalExpr(signal->lhs, ctx, ctx.GetArena());
    obj = ctx.GetClassObject(base.ToUint64());
  }
  if (obj == nullptr || obj->type == nullptr ||
      obj->type->FindProperty(member) == nullptr)
    return kNullClassHandle;
  return obj->handle;
}

inline const ClassTypeInfo* ResolveStaticPropertyClass(
    const Expr* signal, SimContext& ctx, std::string_view& member) {
  const ClassTypeInfo* cls = nullptr;
  if (signal->kind == ExprKind::kIdentifier) {
    member = signal->text;
    cls = ctx.CurrentMethodClass();
  } else if (signal->kind == ExprKind::kMemberAccess &&
             signal->is_scope_resolution && signal->lhs != nullptr) {
    if (signal->lhs->kind == ExprKind::kIdentifier) {
      member = MemberAccessField(signal);
      cls = ctx.FindClassType(signal->lhs->text);
    } else {
      cls = PackageQualifiedClassOf(signal, ctx, member);
    }
  }
  return cls == nullptr ? nullptr : cls->StaticPropertyDeclarer(member);
}

struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  static void AttachEventVarWatcher(Variable* var, const EventExpr& ev,
                                    std::coroutine_handle<> h,
                                    ResumeTarget target,
                                    const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    const Expr* iff_cond = ev.iff_condition;
    const bool kAfterObserved = target.after_observed;
    if (proc) proc->waiting_on_events.push_back(var);
    var->AddWatcher([h, iff_cond, woke = ev, proc, ctx_ptr, consumed,
                     kAfterObserved]() mutable {
      if (proc && !proc->active) return true;
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      if (iff_cond &&
          !EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena()).IsTruthy())
        return false;
      *consumed = true;
      if (proc) proc->woken_by = woke;
      ResumeAfterTrigger(h, proc, *ctx_ptr, kAfterObserved);
      return true;
    });
  }

  static void ResumeAfterTrigger(std::coroutine_handle<> h, Process* proc,
                                 SimContext& ctx, bool after_observed) {
    if (after_observed) {
      ScheduleResume(h, proc, ctx, Region::kReactive);
      return;
    }
    ResumeMaybeReactive(h, proc, ctx);
  }

  static Variable* SequenceEndPoint(const EventExpr& ev, SimContext& ctx) {
    const std::string kKey =
        "__seq_" + std::string(ev.signal->kind == ExprKind::kCall
                                   ? ev.signal->callee
                                   : ev.signal->text);
    Variable* var = ctx.FindVariable(kKey);
    if (var == nullptr) {
      var = ctx.CreateVariable(kKey, 1);
      var->is_event = true;
    }
    return var;
  }

  static void AttachEdgeVarWatcher(Variable* var, const EventExpr& ev,
                                   std::coroutine_handle<> h,
                                   ResumeTarget target,
                                   const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    Logic4Snapshot prev;
    prev.Capture(var->value);
    var->AddWatcher([h, var, prev, edge = ev.edge, iff_cond = ev.iff_condition,
                     woke = ev, ctx_ptr, proc, consumed]() mutable {
      if (proc && !proc->active) return true;
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      var->prev_value = prev;
      bool fired = HandleEdgeEvent(h, var, EdgeSpec{edge, iff_cond},
                                   ResumeTarget{*ctx_ptr, proc});
      if (proc && fired) proc->woken_by = woke;
      prev.Capture(var->value);
      if (fired) *consumed = true;
      return fired;
    });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto consumed = std::make_shared<bool>(false);
    ForgetWaits(proc);
    for (const auto& ev : events) {
      if (!ev.signal) continue;
      if (ev.is_sequence_event) {
        AttachEventVarWatcher(SequenceEndPoint(ev, ctx), ev, h,
                              ResumeTarget{ctx, proc, true}, consumed);
        continue;
      }
      if (AttachTriggeredWatcher(ev, h, proc, consumed)) continue;
      if (ev.signal->kind != ExprKind::kIdentifier &&
          ev.signal->kind != ExprKind::kMemberAccess) {
        AttachCompoundWatchers(ev, h, proc, consumed);
        continue;
      }
      Variable* var = ResolveSignalToVariable(ev.signal, ctx);
      if (!var) {
        AttachClassMemberWatcher(ev, h, proc, consumed);
        continue;
      }
      if (var->is_event) {
        AttachEventVarWatcher(var, ev, h, ResumeTarget{ctx, proc}, consumed);
        continue;
      }
      AttachEdgeVarWatcher(var, ev, h, ResumeTarget{ctx, proc}, consumed);
    }
  }

  static void ForgetWaits(Process* proc) {
    if (proc == nullptr) return;
    proc->woken_by = EventExpr{};
    proc->waiting_on_events.clear();
  }

  void await_resume() const noexcept {
    if (Process* proc = ctx.CurrentProcess()) proc->waiting_on_events.clear();
  }

  static bool CheckEdge(const Variable* var, Edge edge) {
    if (edge == Edge::kNone) {
      const auto& prev = var->prev_value.Get();
      const auto& cur = var->value;
      if (prev.nwords != cur.nwords) return true;
      for (uint32_t i = 0; i < prev.nwords; ++i) {
        if (prev.words[i].aval != cur.words[i].aval ||
            prev.words[i].bval != cur.words[i].bval)
          return true;
      }
      return false;
    }

    return CheckEdgeOnValues(var->prev_value.Get(), var->value, edge);
  }

  static bool EdgeGatePasses(Variable* var, Edge edge) {
    if (CheckEdge(var, edge)) return true;
    var->prev_value.Capture(var->value);
    return false;
  }

  static bool IffGatePasses(Variable* var, const Expr* iff_cond,
                            SimContext& ctx) {
    if (!iff_cond) return true;
    if (EvalExpr(iff_cond, ctx, ctx.GetArena()).IsTruthy()) return true;
    var->prev_value.Capture(var->value);
    return false;
  }

  static bool HandleEdgeEvent(std::coroutine_handle<>& h, Variable* var,
                              const EdgeSpec& spec, ResumeTarget target) {
    if (!EdgeGatePasses(var, spec.edge)) return false;
    if (!IffGatePasses(var, spec.iff_cond, target.ctx)) return false;
    ResumeMaybeReactive(h, target.proc, target.ctx, spec.edge == Edge::kNone);
    return true;
  }

  static void CollectExprIdentifiers(const Expr* e, SimContext& ctx,
                                     std::vector<std::string_view>& out) {
    if (!e) return;
    if (e->kind == ExprKind::kIdentifier) {
      out.push_back(e->text);
      std::vector<std::string_view> elements =
          UnpackedElementNames(e->text, ctx);
      out.insert(out.end(), elements.begin(), elements.end());
      return;
    }
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      auto* flattened = ctx.GetArena().Create<std::string>();
      if (CollectVirtualInterfaceMember(e, ctx, *flattened)) {
        if (!flattened->empty()) out.push_back(*flattened);
        return;
      }
      BuildLhsName(e, *flattened);
      if (!flattened->empty() && ctx.FindVariable(*flattened) != nullptr) {
        out.push_back(*flattened);
        return;
      }
    }
    CollectExprIdentifiers(e->lhs, ctx, out);
    CollectExprIdentifiers(e->rhs, ctx, out);
    CollectExprIdentifiers(e->condition, ctx, out);
    CollectExprIdentifiers(e->true_expr, ctx, out);
    CollectExprIdentifiers(e->false_expr, ctx, out);
    CollectExprIdentifiers(e->base, ctx, out);
    CollectExprIdentifiers(e->index, ctx, out);
    CollectExprIdentifiers(e->index_end, ctx, out);
    for (auto* a : e->args) CollectExprIdentifiers(a, ctx, out);
    for (auto* el : e->elements) {
      CollectExprIdentifiers(el, ctx, out);
    }
  }

  static bool Logic4VecBitsEqual(const Logic4Vec& a, const Logic4Vec& b) {
    if (a.nwords != b.nwords) return false;
    for (uint32_t i = 0; i < a.nwords; ++i) {
      if (a.words[i].aval != b.words[i].aval ||
          a.words[i].bval != b.words[i].bval)
        return false;
    }
    return true;
  }

  static bool CheckEdgeOnValues(const Logic4Vec& prev, const Logic4Vec& cur,
                                Edge edge) {
    uint64_t pa = 0, pb = 0, ca = 0, cb = 0;
    if (prev.nwords > 0) {
      pa = prev.words[0].aval & 1;
      pb = prev.words[0].bval & 1;
    }
    if (cur.nwords > 0) {
      ca = cur.words[0].aval & 1;
      cb = cur.words[0].bval & 1;
    }
    bool prev_is_0 = (pa == 0 && pb == 0);
    bool prev_is_1 = (pa == 1 && pb == 0);
    bool prev_is_xz = (pb == 1);
    bool cur_is_0 = (ca == 0 && cb == 0);
    bool cur_is_1 = (ca == 1 && cb == 0);
    bool pos = (prev_is_0 && !cur_is_0) || (prev_is_xz && cur_is_1);
    bool neg = (prev_is_1 && !cur_is_1) || (prev_is_xz && cur_is_0);
    if (edge == Edge::kPosedge) return pos;
    if (edge == Edge::kNegedge) return neg;
    return pos || neg;
  }

  struct CompoundTrigger {
    bool removed;
    bool resume;
  };

  static Logic4Vec EvalInWaitingProcess(const Expr* e, ResumeTarget target) {
    Process* saved = target.ctx.CurrentProcess();
    target.ctx.SetCurrentProcess(target.proc);
    Logic4Vec value = EvalExpr(e, target.ctx, target.ctx.GetArena());
    target.ctx.SetCurrentProcess(saved);
    return value;
  }

  static CompoundTrigger EvalCompoundTrigger(const CompoundOperand& op,
                                             const EdgeSpec& spec,
                                             ResumeTarget target) {
    if (*op.consumed) return {true, false};
    if (target.proc && !target.proc->active) return {true, false};
    auto cur = EvalInWaitingProcess(op.signal, target);
    if (Logic4VecBitsEqual(cur, op.prev->Get())) return {false, false};
    if (spec.edge != Edge::kNone &&
        !CheckEdgeOnValues(op.prev->Get(), cur, spec.edge)) {
      op.prev->Capture(cur);
      return {false, false};
    }
    op.prev->Capture(cur);
    if (spec.iff_cond &&
        !EvalInWaitingProcess(spec.iff_cond, target).IsTruthy())
      return {false, false};
    *op.consumed = true;
    return {true, true};
  }

  static bool EvalCompoundWatcher(std::coroutine_handle<> h,
                                  const CompoundOperand& op,
                                  const EdgeSpec& spec, ResumeTarget target) {
    auto trigger = EvalCompoundTrigger(op, spec, target);
    if (!trigger.resume) return trigger.removed;
    ResumeMaybeReactive(h, target.proc, target.ctx, spec.edge == Edge::kNone);
    return true;
  }

  static bool EvalMemberWatcher(std::coroutine_handle<> h,
                                const MemberOperand& op, const EdgeSpec& spec,
                                ResumeTarget target) {
    if (*op.consumed) return true;
    if (target.proc && !target.proc->active) return true;
    if (target.proc && target.proc->is_suspended) return false;
    const ClassObject* obj = target.ctx.GetClassObject(op.handle);
    if (obj == nullptr) return true;
    Logic4Vec cur = obj->GetProperty(op.member, target.ctx.GetArena());
    return ResumeOnReadBack(
        h, cur, CompoundOperand{op.prev, op.consumed, nullptr}, spec, target);
  }

  static bool ResumeOnReadBack(std::coroutine_handle<> h, const Logic4Vec& cur,
                               const CompoundOperand& op, const EdgeSpec& spec,
                               ResumeTarget target) {
    if (Logic4VecBitsEqual(cur, op.prev->Get())) return false;
    bool edge_passes = spec.edge == Edge::kNone ||
                       CheckEdgeOnValues(op.prev->Get(), cur, spec.edge);
    op.prev->Capture(cur);
    if (!edge_passes) return false;
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena()).IsTruthy())
      return false;
    *op.consumed = true;
    ResumeMaybeReactive(h, target.proc, target.ctx, spec.edge == Edge::kNone);
    return true;
  }

  static bool EvalStaticPropertyWatcher(std::coroutine_handle<> h,
                                        const StaticPropertyOperand& op,
                                        const EdgeSpec& spec,
                                        ResumeTarget target) {
    if (*op.consumed) return true;
    if (target.proc && !target.proc->active) return true;
    if (target.proc && target.proc->is_suspended) return false;
    auto it = op.cls->static_properties.find(std::string(op.member));
    if (it == op.cls->static_properties.end()) return true;
    return ResumeOnReadBack(h, it->second,
                            CompoundOperand{op.prev, op.consumed, nullptr},
                            spec, target);
  }

  bool AttachStaticPropertyWatcher(const EventExpr& ev,
                                   std::coroutine_handle<> h, Process* proc,
                                   const std::shared_ptr<bool>& consumed) {
    std::string_view member;
    const ClassTypeInfo* cls =
        ResolveStaticPropertyClass(ev.signal, ctx, member);
    if (cls == nullptr) return false;
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(cls->static_properties.at(std::string(member)));
    auto* ctx_ptr = &ctx;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    cls->AddStaticWatcher([h, cls, member, prev, consumed, edge, iff_cond,
                           ctx_ptr, proc]() mutable {
      return EvalStaticPropertyWatcher(
          h, StaticPropertyOperand{cls, member, prev, consumed},
          EdgeSpec{edge, iff_cond}, ResumeTarget{*ctx_ptr, proc});
    });
    return true;
  }

  void AttachClassMemberWatcher(const EventExpr& ev, std::coroutine_handle<> h,
                                Process* proc,
                                const std::shared_ptr<bool>& consumed) {
    if (AttachStaticPropertyWatcher(ev, h, proc, consumed)) return;
    std::string_view member;
    uint64_t handle = ResolveMemberObjectHandle(ev.signal, ctx, member);
    if (handle == kNullClassHandle) return;
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(
        ctx.GetClassObject(handle)->GetProperty(member, ctx.GetArena()));
    auto* ctx_ptr = &ctx;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    ctx.GetClassObject(handle)->AddWatcher([h, handle, member, prev, consumed,
                                            edge, iff_cond, ctx_ptr,
                                            proc]() mutable {
      return EvalMemberWatcher(h, MemberOperand{handle, member, prev, consumed},
                               EdgeSpec{edge, iff_cond},
                               ResumeTarget{*ctx_ptr, proc});
    });
  }

  static Variable* TriggeredMethodEvent(const Expr* signal, SimContext& ctx) {
    const Expr* access = signal->kind == ExprKind::kCall ? signal->lhs : signal;
    if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
        access->is_scope_resolution || access->lhs == nullptr ||
        MemberAccessField(access) != "triggered") {
      return nullptr;
    }
    Variable* event = ResolveSignalToVariable(access->lhs, ctx);
    if (event == nullptr)
      event = ClassEventVariable(access->lhs, ctx, ctx.GetArena());
    return event != nullptr && event->is_event ? event : nullptr;
  }

  bool AttachTriggeredWatcher(const EventExpr& ev, std::coroutine_handle<> h,
                              Process* proc,
                              const std::shared_ptr<bool>& consumed) {
    Variable* event = TriggeredMethodEvent(ev.signal, ctx);
    if (event == nullptr) return false;
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(EvalExpr(ev.signal, ctx, ctx.GetArena()));
    auto* ctx_ptr = &ctx;
    const Expr* signal = ev.signal;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    event->AddWatcher(
        [h, prev, consumed, signal, edge, iff_cond, ctx_ptr, proc]() mutable {
          return EvalCompoundWatcher(h, CompoundOperand{prev, consumed, signal},
                                     EdgeSpec{edge, iff_cond},
                                     ResumeTarget{*ctx_ptr, proc});
        });
    return true;
  }

  void AttachCompoundWatchers(const EventExpr& ev, std::coroutine_handle<> h,
                              Process* proc,
                              const std::shared_ptr<bool>& consumed) {
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(EvalExpr(ev.signal, ctx, ctx.GetArena()));
    auto* ctx_ptr = &ctx;
    const Expr* signal = ev.signal;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    WatchOperandNames(
        signal, ctx,
        [h, prev, consumed, signal, edge, iff_cond, ctx_ptr, proc]() mutable {
          return EvalCompoundWatcher(h, CompoundOperand{prev, consumed, signal},
                                     EdgeSpec{edge, iff_cond},
                                     ResumeTarget{*ctx_ptr, proc});
        });
  }

  static void WatchOperandNames(const Expr* signal, SimContext& ctx,
                                const std::function<bool()>& watcher) {
    std::vector<std::string_view> names;
    CollectExprIdentifiers(signal, ctx, names);
    for (auto name : names) {
      Variable* op_var = ctx.FindVariable(name);
      if (!op_var) continue;
      op_var->AddWatcher(watcher);
    }
  }

  static void ScheduleResume(std::coroutine_handle<> h, Process* proc,
                             SimContext& ctx, Region region) {
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [h, proc, &ctx]() mutable {
      if (!proc->active) return;
      ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, event);
  }

  static void ResumeMaybeReactive(std::coroutine_handle<> h, Process* proc,
                                  SimContext& ctx, bool defer = false) {
    if (proc && proc->is_concurrent_clocked) {
      ScheduleResume(h, proc, ctx, Region::kObserved);
      return;
    }
    if (defer && proc && !proc->is_reactive && !ctx.IsReactiveContext()) {
      ScheduleResume(h, proc, ctx, Region::kActive);
      return;
    }
    if (proc && proc->is_reactive) {
      ScheduleResume(h, proc, ctx, Region::kReactive);
      return;
    }

    if (proc && ctx.IsReactiveContext()) {
      ScheduleResume(h, proc, ctx, Region::kActive);
      return;
    }
    if (proc) {
      auto* saved = ctx.CurrentProcess();
      ctx.SetCurrentProcess(proc);
      h.resume();
      ctx.SetCurrentProcess(saved);
      return;
    }
    h.resume();
  }
};

}  // namespace delta
