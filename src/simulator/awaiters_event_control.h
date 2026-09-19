#pragma once

// The awaiters a suspended process resumes from for a §9.4.2 event control and
// for the §9.4.5 intra-assignment repeat form of it. EventAwaiter arms one
// watcher per operand of an `@(a or b)` list and resumes the coroutine at most
// once per trigger; RepeatEventAwaiter arms a persistent watcher per operand
// and counts occurrences across the whole list until the repeat count is
// reached. The two are here together because they share what an operand is
// made of: ResolveSignalToVariable resolves an operand expression to a
// Variable, EventAwaiter::CheckEdge decides whether an edge qualifies, and
// EventAwaiter::ResumeMaybeReactive decides which region the resume runs in.
// EdgeSpec, ResumeTarget and CompoundOperand are the parameter bundles those
// helpers take.
//
// Split out of src/simulator/awaiters.h, which includes this header and holds
// the awaiters for the other things a process waits on: a delay, a named
// event, a sequence event, a change on any of several variables, an inertial
// delay a change can cancel, a fork join, a cycle delay, a process, a
// semaphore and a mailbox.

#include <coroutine>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

// Parameter-bundle entities for the event-control awaiters below (§9.4.2
// event control, §9.4.5 intra-assignment repeat event control). These mirror
// the real domain objects the watcher helpers operate on, so the helper
// signatures carry one struct per entity instead of a long flat parameter
// list. They are used only by the inline awaiter helpers in this header.

// The edge qualifier and optional iff condition of a single event-control
// operand (§9.4.2). Both come from one EventExpr (ev.edge, ev.iff_condition)
// and always travel together through the edge-gate helpers.
struct EdgeSpec {
  Edge edge;
  const Expr* iff_cond;
};

// The suspended process and its simulation context, i.e. the target to resume
// once a watcher's gates pass. ctx and proc are obtained together from the
// awaiting coroutine and are forwarded as a pair to every resume decision.
struct ResumeTarget {
  SimContext& ctx;
  Process* proc;
};

// §9.4.2 with §8: the per-operand watch state for an event control on a
// member of a class object: the object by its handle (see
// ResolveMemberObjectHandle), the member's name, the baseline the change is
// measured from, and the guard the operands of one event control share.
struct MemberOperand {
  uint64_t handle;
  std::string_view member;
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
};

// §9.4.2 with §8.9: the per-operand watch state for an event control on a
// static property of a class: the class (see ResolveStaticPropertyClass), the
// property's name, the baseline the change is measured from, and the guard
// the operands of one event control share.
struct StaticPropertyOperand {
  const ClassTypeInfo* cls;
  std::string_view member;
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
};

// The shared per-operand watch state for a compound (non-identifier) event
// expression operand: the previous evaluated value, the once-only consumed
// guard shared across sibling operand watchers, and the signal expression to
// re-evaluate. One object describes a single compound operand being watched.
struct CompoundOperand {
  const std::shared_ptr<Logic4Snapshot>& prev;
  const std::shared_ptr<bool>& consumed;
  const Expr* signal;
};

// The member a member-access event-control operand names: `clk` in `v.clk`.
// The parser leaves the name either in the rhs identifier or in the node's
// own text, as TryVirtualInterfaceMember in src/simulator/eval_expr.cpp reads
// it, so both places are looked at here.
inline std::string_view MemberAccessField(const Expr* signal) {
  if (signal->rhs && signal->rhs->kind == ExprKind::kIdentifier)
    return signal->rhs->text;
  return signal->text;
}

// The name of the bound instance's component that a member access through a
// virtual interface denotes, `top.dif.clk` for `v.clk` with `v` bound to
// `top.dif`, written to `name`. Answers true when the base is a virtual
// interface -- a variable declared so, a property declared so of the class
// whose method the waiting process is running, which is the clause's own
// transactor waiting on `@(posedge bus.grant)`, or a property declared so of
// the object a handle expression denotes, `@(posedge d.vif.clk)` from a
// module holding the transactor `d` -- leaving `name` empty for an unbound
// one; false for any other base, with `name` untouched. Unlike
// ResolveVirtualInterfaceSignal it reports nothing: it serves the
// compound-operand path, where the expression is also evaluated as a whole
// and that evaluation reports an unbound base.
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

// §25.9: a virtual interface variable represents an interface instance, and
// once it is initialized every component of that instance is reached through
// it by the dot notation -- the clause's own transactor waits on
// `@(posedge bus.grant)` with `bus` such a variable. The variable an event
// control has to watch is therefore the bound instance's own, which is what a
// read through the variable reaches (TryVirtualInterfaceMember in
// src/simulator/eval_expr.cpp) and what a write reaches
// (ResolveVirtualInterfaceField in src/simulator/statement_assign.cpp).
//
// Answers true when the operand's base names a virtual interface variable,
// bound or not, and then leaves in *out the instance's variable for the
// member, or nullptr where the base is unbound. §25.9 makes a reference
// through an unbound virtual interface a fatal run-time error, so that case
// is reported here as the read path reports it rather than left to arm no
// watcher and wait for nothing. Answers false for any other base, which the
// caller then resolves as before.
//
// Before this, `@(posedge v.clk)` fell through to the flattened name `v.clk`,
// which SimContext::FindVariable does not hold -- the virtual interface
// variable has no component of its own, the instance has them -- so the
// operand was skipped and the process was never resumed.
inline bool ResolveVirtualInterfaceSignal(const Expr* signal, SimContext& ctx,
                                          Variable** out) {
  *out = nullptr;
  std::string target;
  if (!CollectVirtualInterfaceMember(signal, ctx, target)) return false;
  if (target.empty()) {
    ctx.GetDiag().Error(signal->range.start,
                        "reference through a null virtual interface",
                        Subclause("25.9"));
    return true;
  }
  *out = ctx.FindVariable(target);
  return true;
}

// Resolves a member-access event-control signal down to a Variable*. Tries a
// clocking-block member first, then a component reached through a virtual
// interface variable, then falls back to a flattened hierarchical name
// lookup. Returns nullptr when none resolves.
inline Variable* ResolveMemberAccessSignal(const Expr* signal,
                                           SimContext& ctx) {
  Variable* var = nullptr;
  if (signal->lhs && signal->lhs->kind == ExprKind::kIdentifier) {
    auto* mgr = ctx.GetClockingManager();
    std::string_view member = MemberAccessField(signal);
    if (mgr && !member.empty())
      var = mgr->ResolveClockingMember(signal->lhs->text, member, ctx);
  }
  if (!var && ResolveVirtualInterfaceSignal(signal, ctx, &var)) return var;
  if (!var) {
    std::string hier_name;
    BuildLhsName(signal, hier_name);
    var = ctx.FindVariable(hier_name);
  }
  return var;
}

// Resolves an event-control signal expression down to a Variable*. Handles
// plain identifiers, clocking-block member accesses, and hierarchical names.
// Returns nullptr when the expression is not one of these forms (e.g. a
// compound expression) or cannot be resolved.
inline Variable* ResolveSignalToVariable(const Expr* signal, SimContext& ctx) {
  if (signal->kind == ExprKind::kIdentifier) {
    // §23.6: a leading `$root` makes the name absolute from the top of the
    // instantiated design, and the parser keeps it in Expr::scope_prefix
    // rather than in the identifier's text (Parser::MakeSysScopePrefix in
    // src/parser/expr_parser_calls.cpp). Reading the text alone drops it and
    // resolves the name in whichever instance is running, so the whole name is
    // spelled out here. BuildLhsName writes both fields, and the member-access
    // branch below already reaches SimContext::FindVariable through it.
    //
    // Only `$root` is spelled out. Expr::scope_prefix also carries the §23.7.1
    // package and `$unit` scope resolution prefixes, which are separated by ::
    // rather than by the period BuildLhsName writes and are not hierarchical
    // names at all.
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

// §9.4.2 with §8: whether the operand's base denotes a class object -- `this`
// or `super` inside a method, a class-typed variable, a class-typed property
// of the running method's object, or a member access down such a base. Only
// such a base is evaluated to a handle below, so a hierarchical name that
// resolved to nothing stays as it was, skipped, rather than evaluated for a
// diagnostic it never raised.
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

// §9.4.2 with §8.5, §8.6 and §8.11: the object whose member the event-control
// operand names, and the member, when the operand is one -- `p.status`
// through a handle or a chain of them, `this.status`, or the bare `status`
// of the running method's object -- else null. The object is answered by its
// handle rather than a pointer, since the garbage collector of §8.4 may sweep
// it while a process still waits, and the waiter then finds nothing to read.
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

// §9.4.2 with §8.9 and §8.10: the class whose static property the operand
// names, and the property, when the operand is one -- `C::n` through the
// class scope operator, or the bare `n` inside a method of C, which §8.10
// lets a method name unqualified -- else null. A static property is the
// class's own storage, one for every object and for no object at all, so what
// a process waiting on it has to arm on is the class, not an object: a write
// through `C::n` reaches no object's watchers, and a static method has no
// `this` to arm on in the first place.
inline const ClassTypeInfo* ResolveStaticPropertyClass(
    const Expr* signal, SimContext& ctx, std::string_view& member) {
  const ClassTypeInfo* cls = nullptr;
  if (signal->kind == ExprKind::kIdentifier) {
    member = signal->text;
    cls = ctx.CurrentMethodClass();
  } else if (signal->kind == ExprKind::kMemberAccess &&
             signal->is_scope_resolution && signal->lhs != nullptr &&
             signal->lhs->kind == ExprKind::kIdentifier) {
    member = MemberAccessField(signal);
    cls = ctx.FindClassType(signal->lhs->text);
  }
  if (cls == nullptr || cls->static_properties.find(std::string(member)) ==
                            cls->static_properties.end())
    return nullptr;
  return cls;
}

struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  // Arms a watcher on a named-event variable that resumes the suspended
  // coroutine (respecting active/suspended process state) once when triggered.
  //
  // §9.4.2.3: an `iff` qualifier on the operand gates that resume, so a trigger
  // arriving while the condition is false leaves the process suspended and the
  // watcher armed for the next one.
  static void AttachEventVarWatcher(Variable* var, const Expr* iff_cond,
                                    std::coroutine_handle<> h,
                                    ResumeTarget target,
                                    const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher([h, iff_cond, proc, ctx_ptr, consumed]() mutable {
      if (proc && !proc->active) return true;
      // A sibling operand of the same event control already resumed this
      // await; the coroutine has moved on, so retire this stale watcher.
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      if (iff_cond &&
          !EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena()).IsTruthy())
        return false;
      *consumed = true;
      ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    });
  }

  // Arms an edge-sensitive watcher on a value-carrying variable, delegating
  // the edge/iff evaluation and resume decision to HandleEdgeEvent.
  static void AttachEdgeVarWatcher(Variable* var, const EventExpr& ev,
                                   std::coroutine_handle<> h,
                                   ResumeTarget target,
                                   const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    // Per-watcher snapshot of the value as of arming. The single shared
    // var->prev_value is clobbered when one of several coroutines waiting on
    // the same signal's edge resumes and re-arms synchronously mid-notify,
    // which starves every later watcher in that drain (e.g. only the first of
    // two `always @(posedge clk)` blocks would ever fire). Each watcher keeps
    // its own baseline and restores it before delegating to the shared edge
    // logic, so the detections stay independent.
    //
    // It is a Logic4Snapshot, which owns the words it captured, rather than a
    // Logic4Vec, which would share the ones var->value holds. A member
    // assignment writes through those words instead of replacing them, so a
    // sharing baseline moves with the value it is there to be compared
    // against and the change is never seen (#3358).
    Logic4Snapshot prev;
    prev.Capture(var->value);
    var->AddWatcher([h, var, prev, edge = ev.edge, iff_cond = ev.iff_condition,
                     ctx_ptr, proc, consumed]() mutable {
      if (proc && !proc->active) return true;
      // Another operand of the same `@(a or b)` event control already resumed
      // this await; retire this stale sibling so it cannot re-fire the handle.
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      var->prev_value = prev;
      bool fired = HandleEdgeEvent(h, var, EdgeSpec{edge, iff_cond},
                                   ResumeTarget{*ctx_ptr, proc});
      prev.Capture(var->value);
      if (fired) *consumed = true;
      return fired;
    });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    // §9.4.2: an `@(a or b ...)` event control resumes its process at most once
    // per trigger. All operand watchers armed by this await share one guard so
    // that the first to fire retires the rest, even when several operands name
    // the same signal (e.g. `posedge clk or negedge clk`).
    auto consumed = std::make_shared<bool>(false);
    for (const auto& ev : events) {
      if (!ev.signal) continue;
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
        AttachEventVarWatcher(var, ev.iff_condition, h, ResumeTarget{ctx, proc},
                              consumed);
        continue;
      }
      AttachEdgeVarWatcher(var, ev, h, ResumeTarget{ctx, proc}, consumed);
    }
  }

  void await_resume() const noexcept {}

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

  // Evaluates the edge gate for an edge-sensitive variable watcher. On a
  // qualifying edge returns true; otherwise resyncs prev_value and returns
  // false so the watcher stays armed without resuming.
  static bool EdgeGatePasses(Variable* var, Edge edge) {
    if (CheckEdge(var, edge)) return true;
    var->prev_value.Capture(var->value);
    return false;
  }

  // §9.4.2.3: evaluates the optional iff condition for an edge-sensitive
  // variable watcher. Returns true when there is no condition or the condition
  // is true; otherwise resyncs prev_value and returns false. §12.4 decides what
  // true means, so a condition is true when any of its bits is 1 and false when
  // it is zero, x or z. Logic4Vec::IsTruthy answers that over the whole value,
  // where ToUint64 reads the low 64 bits and would call a wider condition false
  // whenever every bit it set sits above them.
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

  // The names a compound event expression watches. §9.4.2 admits any expression
  // as an event_expression and puts no condition on the names in it, so a
  // hierarchical name stands there exactly as a local one does.
  //
  // A member access is flattened rather than descended into. Descending
  // collected `u` and `a` from `u.a` as two bare names, neither of which names
  // anything in the referencing instance, so `@(u.a & u.b)` armed watchers on
  // nothing and the process waited forever -- while `@(u.a)` worked, that going
  // to ResolveSignalToVariable, which flattens. The two paths disagreed about
  // what one name denotes, which no clause asks for. BuildLhsName is what the
  // direct path builds the name with, so both now build the same one, and
  // SimContext::FindVariable resolves a dotted name from inside any instance.
  //
  // EvalExpr needed nothing: it answers a kMemberAccess through
  // EvalMemberAccess, so the recomputation EvalCompoundWatcher makes already
  // read the variable this now watches.
  //
  // The `::` form is left to the descent below. A package or class scope
  // resolution is not a hierarchical name, and BuildLhsName writes the period
  // that joins one.
  //
  // A member access is flattened only where the flattened name resolves to a
  // variable. `q.size()` is a member access too -- a queue method call -- and
  // `q.size` names nothing, so that one falls through to the descent below and
  // is watched through `q` as it always was. The test on the name rather than
  // on the node's shape is what keeps every method call on that path without
  // this walk having to enumerate them.
  //
  // §25.9: `vif.a` in `@(vif.a & vif.b)` is a component of the interface
  // instance the virtual interface variable is bound to, so what is watched
  // is that instance's variable under its own name, the one the direct path
  // resolves through ResolveVirtualInterfaceSignal. The flattened `vif.a`
  // names nothing, and descending to `vif` watched a handle no component
  // write ever touches. An unbound base contributes no name; the evaluation
  // of the whole expression that AttachCompoundWatchers makes before
  // collecting reports the §25.9 error for it.
  //
  // The arena owns the flattened name, the collected names being string_views
  // that outlive this call in the watcher closures.
  static void CollectExprIdentifiers(const Expr* e, SimContext& ctx,
                                     std::vector<std::string_view>& out) {
    if (!e) return;
    if (e->kind == ExprKind::kIdentifier) {
      out.push_back(e->text);
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

  // Body of a compound-expression operand watcher. Re-evaluates the whole
  // signal expression, applies the change/edge/iff gates against the shared
  // previous value, and on a genuine triggering change marks the shared guard
  // consumed and resumes the process once. Returns the AddWatcher convention
  // (true removes the watcher, false keeps it armed).
  // Result of a compound-watcher trigger evaluation. `removed` carries the
  // AddWatcher return value to use when the watcher is not resuming;
  // `resume` is set only when every gate passed and the process should run.
  struct CompoundTrigger {
    bool removed;
    bool resume;
  };

  // Applies the change/edge/iff gates for a compound-expression operand
  // watcher against the shared previous value, updating *prev in place. The
  // shared `consumed` guard ensures the resume happens at most once across all
  // sibling watchers. Does not perform the resume itself.
  static CompoundTrigger EvalCompoundTrigger(const CompoundOperand& op,
                                             const EdgeSpec& spec,
                                             ResumeTarget target) {
    if (*op.consumed) return {true, false};
    if (target.proc && !target.proc->active) return {true, false};
    auto cur = EvalExpr(op.signal, target.ctx, target.ctx.GetArena());
    if (Logic4VecBitsEqual(cur, op.prev->Get())) return {false, false};
    if (spec.edge != Edge::kNone &&
        !CheckEdgeOnValues(op.prev->Get(), cur, spec.edge)) {
      op.prev->Capture(cur);
      return {false, false};
    }
    op.prev->Capture(cur);
    // §9.4.2.3 with §12.4: the guard is true when any bit of it is 1.
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena()).IsTruthy())
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

  // §9.4.2: an implicit event on a member of a class object is detected on a
  // change of that member's value, and an edge event on its LSB, as for any
  // other expression. The operand resolves to no variable -- the member is a
  // slot of the object, not a Variable -- so this arms on the object itself,
  // which every member write reaches through
  // SimContext::NotifyClassHandleWatchers, and reads the member back from the
  // object at each notification. Before this the operand was skipped and the
  // process waited for ever: `@(p.status)` at module scope, `@(status)` and
  // `@(this.status)` inside a method, `@(posedge h.flag)`.
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

  // The gates a watcher that reads its operand back on each notification
  // applies to the value read, `cur`: §9.4.2's change of value against the
  // baseline, the edge on the LSB where one is asked for, and §9.4.2.3's iff
  // condition. On a genuine trigger it marks the shared guard consumed and
  // resumes the process once; the answer is the AddWatcher convention. The
  // operand bundle carries only the baseline and the guard here; its signal
  // is unused, the caller having read the value itself.
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

  // §9.4.2 with §8.9: the watcher body for a static property of a class. It
  // is armed on the class, which every write to the class's own storage
  // reaches through ClassTypeInfo::NotifyStaticWatchers, and reads the
  // property back from that storage at each notification. Before this
  // `@(C::n)` resolved to no variable and no object, so the operand was
  // skipped and the process waited for ever.
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

  // Arms on the class when the operand names a static property, answering
  // whether it did. It is asked before the object form: inside an instance
  // method the bare name of a static property is also found by
  // ClassTypeInfo::FindProperty, and arming on the object there would miss
  // every write made through `C::n` or from a static method.
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

  void AttachCompoundWatchers(const EventExpr& ev, std::coroutine_handle<> h,
                              Process* proc,
                              const std::shared_ptr<bool>& consumed) {
    // The baseline is taken before the names are collected: this evaluation
    // is what reports a §25.9 reference through an unbound virtual interface
    // in the operand, and it has to run even when that leaves no name to
    // watch.
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(EvalExpr(ev.signal, ctx, ctx.GetArena()));
    std::vector<std::string_view> names;
    CollectExprIdentifiers(ev.signal, ctx, names);
    if (names.empty()) return;
    auto* ctx_ptr = &ctx;
    const Expr* signal = ev.signal;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    for (auto name : names) {
      Variable* op_var = ctx.FindVariable(name);
      if (!op_var) continue;
      op_var->AddWatcher([h, prev, consumed, signal, edge, iff_cond, ctx_ptr,
                          proc]() mutable {
        return EvalCompoundWatcher(h, CompoundOperand{prev, consumed, signal},
                                   EdgeSpec{edge, iff_cond},
                                   ResumeTarget{*ctx_ptr, proc});
      });
    }
  }

  // Schedule `h` to resume in `region` at the current time, bound to `proc`.
  // Used by the deferred/reactive branches of ResumeMaybeReactive so the
  // coroutine runs in its own scheduling slot rather than synchronously inside
  // the caller's NotifyWatchers loop.
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
    // §16.5: "Concurrent assertions are evaluated in the Observed region." A
    // process carrying one is therefore resumed into that region whatever edge
    // its clocking event names, rather than synchronously inside the process
    // that assigned the clock, where `cond = 1; clk = 1;` and
    // `clk = 1; cond = 1;` would reach two different verdicts.
    if (proc && proc->is_concurrent_clocked) {
      ScheduleResume(h, proc, ctx, Region::kObserved);
      return;
    }
    // §9.2.2.2 / §4: a level-sensitive (non-edge) process triggered by another
    // process's blocking write must observe *settled* inputs, so its evaluation
    // is scheduled into the Active region rather than resumed synchronously in
    // the middle of the writer's NotifyWatchers loop. Otherwise an always @*
    // reading two signals that the writer sets in sequence (a=..; b=..) would
    // fire on the first write and read the second signal before it is updated.
    // Edge-sensitive (posedge/negedge) resumes stay synchronous.
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
    // §9.4: the coroutine being resumed belongs to `proc`. A synchronous resume
    // runs inside whatever process is currently executing (e.g. the one that
    // drove the awaited signal in NotifyWatchers), so set the current process
    // to `proc` for the duration of the resume and restore it afterward; this
    // keeps per-process state (FlushPendingViolations, name lookup) correct
    // without disturbing the caller's NotifyWatchers loop.
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

// §9.4.5 intra-assignment repeat event control. A plain event control is
// awaited once, but the repeat form has to accumulate a fixed number of event
// occurrences across the whole OR-list. Each operand keeps a single persistent
// watcher (rather than being re-armed once per occurrence), so two edges in the
// same time step on different operands are each counted, and a shared guard
// resumes the issuing process exactly once when the target count is reached —
// any later sibling watcher that fires afterwards removes itself without
// touching the already-resumed coroutine.
struct RepeatEventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;
  uint64_t count;

  bool await_ready() const noexcept { return count == 0; }

  // Arms a persistent watcher on a named-event operand. Each occurrence is
  // forwarded to tally once the active/suspended gates pass, and §9.4.2.3's
  // `iff` qualifier gates it as it gates an edge operand: an occurrence
  // arriving while the condition is false is not one of the occurrences the
  // repeat is counting.
  template <typename TallyFn>
  static void ArmEventOperand(Variable* var, const Expr* iff_cond,
                              ResumeTarget target,
                              const std::shared_ptr<bool>& done,
                              const TallyFn& tally) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher([iff_cond, ctx_ptr, proc, done, tally]() mutable {
      if (*done) return true;
      if (proc && !proc->active) return true;
      if (proc && proc->is_suspended) return false;
      if (iff_cond &&
          !EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena()).IsTruthy())
        return false;
      return tally();
    });
  }

  // Arms a persistent edge-sensitive watcher on a value-carrying operand,
  // forwarding qualifying edges (after the iff gate) to tally.
  // Edge-watcher gate result. `passed` is true when a qualifying edge (and the
  // iff condition) was seen and the occurrence should be tallied; otherwise
  // `keep_armed_return` carries the AddWatcher value to return.
  struct EdgeOperandGate {
    bool passed;
    bool keep_armed_return;
  };

  // Applies the active/suspended/edge/iff gates for a repeat edge operand
  // watcher, resyncing var->prev_value on each non-tally exit. Returns whether
  // the occurrence should be tallied along with the watcher return value to use
  // when it should not.
  static EdgeOperandGate EvalEdgeOperandGate(Variable* var,
                                             const EdgeSpec& spec,
                                             const std::shared_ptr<bool>& done,
                                             ResumeTarget target) {
    if (*done) return {false, true};
    if (target.proc && !target.proc->active) return {false, true};
    if (target.proc && target.proc->is_suspended) return {false, false};
    if (!EventAwaiter::CheckEdge(var, spec.edge)) {
      var->prev_value.Capture(var->value);
      return {false, false};
    }
    // §9.4.2.3 with §12.4: the guard is true when any bit of it is 1.
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena())
             .IsTruthy()) {
      var->prev_value.Capture(var->value);
      return {false, false};
    }
    var->prev_value.Capture(var->value);
    return {true, false};
  }

  template <typename TallyFn>
  static void ArmEdgeOperand(Variable* var, const EventExpr& ev,
                             const std::shared_ptr<bool>& done,
                             ResumeTarget target, const TallyFn& tally) {
    var->prev_value.Capture(var->value);
    Edge edge = ev.edge;
    const Expr* iff_cond = ev.iff_condition;
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher(
        [var, edge, iff_cond, ctx_ptr, proc, done, tally]() mutable {
          auto gate = EvalEdgeOperandGate(var, EdgeSpec{edge, iff_cond}, done,
                                          ResumeTarget{*ctx_ptr, proc});
          if (!gate.passed) return gate.keep_armed_return;
          return tally();
        });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto remaining = std::make_shared<uint64_t>(count);
    auto done = std::make_shared<bool>(false);
    auto* ctx_ptr = &ctx;

    // Counts one occurrence and, when the target is reached, resumes the
    // process once. Returning false keeps the watcher armed for the next
    // occurrence; returning true removes it.
    auto tally = [h, proc, ctx_ptr, remaining, done]() {
      if (*remaining > 0) --(*remaining);
      if (*remaining == 0) {
        *done = true;
        EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
        return true;
      }
      return false;
    };

    for (const auto& ev : events) {
      if (!ev.signal) continue;
      Variable* var = ResolveSignalToVariable(ev.signal, ctx);
      if (!var) continue;
      if (var->is_event) {
        ArmEventOperand(var, ev.iff_condition, ResumeTarget{ctx, proc}, done,
                        tally);
        continue;
      }
      ArmEdgeOperand(var, ev, done, ResumeTarget{ctx, proc}, tally);
    }
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
