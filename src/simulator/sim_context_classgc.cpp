#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/class_gc_roots.h"
#include "simulator/class_object.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/file_monitor.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/scope.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_file_tables.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

uint64_t SimContext::AllocateClassObject(ClassObject* obj) {
  uint64_t id = next_handle_id_++;
  // §18.14.1 object stability: seed the new object's RNG with the next random
  // value drawn from the active stream. While a thread is running this is the
  // creating thread's generator, so an object built with new inherits the next
  // value from that thread; with no thread current the draw comes from the
  // initialization RNG of the instance being built, covering objects created
  // by a static declaration initializer. Each object therefore receives its
  // own stream.
  obj->rng_seed = DrawSeedForChild();
  class_objects_[id] = obj;
  obj->handle = id;
  obj->ref_count = 1;
  scheduler_.NoteClassObjectMade();
  return id;
}

ClassObject* SimContext::GetClassObject(uint64_t handle) const {
  if (handle == kNullClassHandle) return nullptr;
  auto it = class_objects_.find(handle);
  return (it != class_objects_.end()) ? it->second : nullptr;
}

void SimContext::DeallocateClassObject(uint64_t handle) {
  class_objects_.erase(handle);
}

void SimContext::RetainObject(uint64_t handle) {
  if (handle == kNullClassHandle) return;
  auto it = class_objects_.find(handle);
  if (it != class_objects_.end()) {
    ++it->second->ref_count;
  }
}

void SimContext::ReleaseObject(uint64_t handle) {
  if (handle == kNullClassHandle) return;
  auto it = class_objects_.find(handle);
  if (it != class_objects_.end() && it->second->ref_count > 0) {
    --it->second->ref_count;
  }
}

Reachability SimContext::GetReachability(uint64_t handle) const {
  if (handle == kNullClassHandle) return Reachability::kUnreachable;
  auto it = class_objects_.find(handle);
  if (it == class_objects_.end()) return Reachability::kUnreachable;
  if (it->second->ref_count > 0) return Reachability::kStronglyReachable;

  for (const auto* wr : weak_references_) {
    if (wr->referent_handle == handle) return Reachability::kWeaklyReachable;
  }
  return Reachability::kUnreachable;
}

namespace {

// Clears every weak reference whose referent is no longer in the live set.
void ClearDeadWeakReferences(
    const std::unordered_set<WeakReference*>& weak_references,
    const std::unordered_set<uint64_t>& live) {
  for (auto* wr : weak_references) {
    if (wr->referent_handle != kNullClassHandle &&
        !live.count(wr->referent_handle)) {
      wr->Clear();
    }
  }
}

// Erases every class object that is not live, zeroing its ref count before
// removal, and tells the VPI of each, whose handles the reclaim releases
// (§37.2.2).
void SweepDeadObjects(
    const std::unordered_set<uint64_t>& live,
    std::unordered_map<uint64_t, ClassObject*>& class_objects) {
  for (auto it = class_objects.begin(); it != class_objects.end();) {
    if (!live.count(it->first)) {
      GetGlobalVpiContext().NoteObjectReclaimed(*it->second);
      it->second->ref_count = 0;
      it = class_objects.erase(it);
    } else {
      ++it;
    }
  }
}

// §8.29: the design's variables are roots, each structure among them read by
// the layout `tables` records for it as well.
void MarkVariables(
    ClassGcMarker& mark, const DeclaredNameTables& tables,
    const std::unordered_map<std::string_view, Variable*>& variables) {
  for (const auto& [name, var] : variables) {
    mark.Var(var);
    // §7.2: a structure's class-typed members, where its layout puts them.
    const StructTypeInfo* layout = tables.GetVariableStructType(name);
    if (layout != nullptr) mark.Fields(var->value, *layout);
  }
}

// §8.29: the roots of the scopes of the process the run last switched to, the
// static frames, and the objects that process's method calls run on.
void MarkStorage(
    ClassGcMarker& mark, const std::vector<Scope>& scopes,
    const std::unordered_map<std::string_view,
                             std::unordered_map<std::string_view, Variable*>>&
        static_frames,
    const std::vector<ClassObject*>& this_stack) {
  for (const Scope& scope : scopes) mark.InScope(scope);
  for (const auto& [owner, frame] : static_frames) {
    for (const auto& [name, var] : frame) mark.Var(var);
  }
  for (const ClassObject* obj : this_stack) {
    if (obj != nullptr) mark.Handle(obj->handle);
  }
}

// §8.29: the stacks every other process parked or carries, and those the
// $monitor and $fmonitor callers keep.
void MarkProcesses(
    ClassGcMarker& mark, const Scheduler& scheduler,
    const Process* monitor_caller,
    const std::vector<std::unique_ptr<FileMonitor>>& file_monitors) {
  for (const Process* proc : scheduler.Threads()) mark.Stacks(*proc);
  for (const Process* proc : scheduler.Carriers()) mark.Stacks(*proc);
  if (monitor_caller != nullptr) mark.Stacks(*monitor_caller);
  for (const auto& monitor : file_monitors) {
    if (monitor->caller != nullptr) mark.Stacks(*monitor->caller);
  }
}

// The run's containers and classes, which MarkContainers reads as roots.
struct RunContainers {
  const std::unordered_map<std::string_view, QueueObject*>& queues;
  const std::unordered_map<std::string_view, AssocArrayObject*>& assocs;
  const std::unordered_map<std::string_view, MailboxObject*>& mailboxes;
  const std::vector<const MailboxObject*>& held_mailboxes;
  const std::unordered_map<std::string_view, ClassTypeInfo*>& class_types;
};

// §8.29: the queues, associative arrays and mailboxes the run holds by name,
// by handle or in a container, the arrays dynamic structure members hold, and
// each class's static properties.
void MarkContainers(ClassGcMarker& mark, const RunContainers& run) {
  for (const auto& [name, queue] : run.queues) mark.Queue(queue);
  for (const QueueObject* queue : DynMemberQueues()) mark.Queue(queue);
  for (const auto& [name, assoc] : run.assocs) mark.Assoc(assoc);
  for (const auto& [name, mailbox] : run.mailboxes) mark.Mailbox(mailbox);
  for (const MailboxObject* mailbox : run.held_mailboxes) {
    mark.Mailbox(mailbox);
  }
  for (const auto& [name, type] : run.class_types) {
    if (type != nullptr) mark.Statics(*type);
  }
}

}  // namespace

void SimContext::NotifyClassHandleWatchers(uint64_t handle) {
  if (handle == kNullClassHandle) return;
  auto notify_if_designates = [&](std::string_view name, Variable* var) {
    if (!var || !var_class_types_.count(name)) return;
    if (var->value.ToUint64() == handle) var->NotifyWatchers();
  };
  // The variables a handle can be held in by name: the design's variables,
  // every open scope, and every static frame.
  for (const auto& [name, var] : variables_) notify_if_designates(name, var);
  for (const auto& scope : scope_stack_) {
    for (const auto& [name, var] : scope.vars) notify_if_designates(name, var);
  }
  for (const auto& [func, frame] : static_frames_) {
    for (const auto& [name, var] : frame) notify_if_designates(name, var);
  }
  // §9.4.2: and the processes watching the object itself, which an event
  // control on one of its members armed there (EventAwaiter in
  // src/simulator/awaiters_event_control.h).
  if (auto* obj = GetClassObject(handle)) obj->NotifyWatchers();
}

void SimContext::CollectGarbage() {
  if (class_objects_.empty()) {
    scheduler_.NoteClassCollection(0);
    return;
  }

  // §8.29: an object is strongly reachable while a class handle in any active
  // scope refers to it, and the places the run keeps one are the roots below;
  // the objects any of them reach are reachable too.
  std::unordered_set<uint64_t> live;
  ClassGcMarker mark(class_objects_, live);
  MarkVariables(mark, *this, variables_);
  MarkStorage(mark, scope_stack_, static_frames_, this_stack_);
  MarkProcesses(mark, scheduler_, monitor_caller_.get(), files_.monitors);
  MarkContainers(mark, {queues_, assoc_arrays_, mailboxes_, HeldMailboxes(),
                        class_types_});
  for (const auto& [handle, count] : scheduler_.PinnedHandles()) {
    mark.Handle(handle);
  }
  mark.Propagate();

  ClearDeadWeakReferences(weak_references_, live);
  SweepDeadObjects(live, class_objects_);
  scheduler_.NoteClassCollection(class_objects_.size());
}

void SimContext::RegisterWeakReference(WeakReference* wr) {
  if (wr) weak_references_.insert(wr);
}

void SimContext::UnregisterWeakReference(WeakReference* wr) {
  weak_references_.erase(wr);
}

uint64_t SimContext::AllocateWeakReference(uint64_t referent_handle,
                                           Arena& arena) {
  auto* wr = arena.Create<WeakReference>();
  wr->referent_handle = referent_handle;
  uint64_t handle = next_handle_id_++;
  weak_ref_by_handle_[handle] = wr;
  RegisterWeakReference(wr);
  return handle;
}

WeakReference* SimContext::FindWeakReferenceByHandle(uint64_t handle) const {
  auto it = weak_ref_by_handle_.find(handle);
  return (it != weak_ref_by_handle_.end()) ? it->second : nullptr;
}

void SimContext::PushThis(ClassObject* obj) { this_stack_.push_back(obj); }

ClassObject* SimContext::SetConstraintCallerThis(ClassObject* obj) {
  ClassObject* previous = constraint_caller_this_;
  constraint_caller_this_ = obj;
  return previous;
}

void SimContext::PopThis() {
  if (!this_stack_.empty()) this_stack_.pop_back();
}

ClassObject* SimContext::CurrentThis() const {
  return this_stack_.empty() ? nullptr : this_stack_.back();
}

uint64_t SimContext::CurrentThisHandle() const {
  const ClassObject* self = CurrentThis();
  return self ? self->handle : kNullClassHandle;
}

uint64_t SimContext::RegisterProcessHandle(Process* proc) {
  for (auto& [id, p] : process_handles_) {
    if (p == proc) return id;
  }
  uint64_t id = next_process_handle_id_++;
  process_handles_[id] = proc;
  return id;
}

Process* SimContext::FindProcessByHandle(uint64_t handle) const {
  auto it = process_handles_.find(handle);
  return it != process_handles_.end() ? it->second : nullptr;
}

// §20.11 Table 20-6: the assertion_type bit of the violation reports a unique,
// unique0 or priority statement generates.
static uint32_t ViolationTypeBit(CaseQualifier qual) {
  switch (qual) {
    case CaseQualifier::kUnique0:
      return static_cast<uint32_t>(AssertionTypeBit::kUnique0);
    case CaseQualifier::kPriority:
      return static_cast<uint32_t>(AssertionTypeBit::kPriority);
    default:
      return static_cast<uint32_t>(AssertionTypeBit::kUnique);
  }
}

void SimContext::AddPendingViolation(SourceLoc loc, std::string msg,
                                     Subclause subclause, CaseQualifier qual) {
  // §20.11: an Off or a Kill that selects the report's type adds no new report
  // to the queue until an On; one already queued is left to mature, or to the
  // Kill's flush (AbortKilledAttempts).
  uint32_t type_bit = ViolationTypeBit(qual);
  std::string scope =
      assert_controls_.NamesScopes() ? ScopeHierName(*this) : std::string();
  if (!assert_controls_.StatusOf({type_bit, 0, scope, {}}).checking) return;
  if (current_process_) {
    current_process_->pending_violations.push_back(
        {loc, std::move(msg), subclause.Text(), type_bit, std::move(scope)});

    auto* ev = scheduler_.GetEventPool().Acquire();
    Process* proc = current_process_;
    ev->callback = [this, proc]() {
      for (auto& v : proc->pending_violations) {
        diag_.Warning(v.loc, std::move(v.msg), Subclause(v.subclause));
      }
      proc->pending_violations.clear();
    };
    scheduler_.ScheduleEvent(scheduler_.CurrentTime(), Region::kObserved, ev);
  } else {
    diag_.Warning(loc, std::move(msg), subclause);
  }
}

void SimContext::FlushPendingViolations() {
  if (current_process_) {
    current_process_->pending_violations.clear();
  }
}

void SimContext::MaturePendingViolations() {
  if (current_process_) {
    for (auto& v : current_process_->pending_violations) {
      diag_.Warning(v.loc, std::move(v.msg), Subclause(v.subclause));
    }
    current_process_->pending_violations.clear();
  }
}

void SimContext::FlushPendingDeferredReports() {
  // §16.4.2: bumping the generation invalidates every deferred report this
  // process has queued but not yet run this time step; those reports observe
  // the mismatch when their region fires and skip execution.
  if (current_process_) {
    current_process_->deferred_report_generation++;
    // §16.14.6.2: the same points are the procedural assertion flush points,
    // where the pending instances of the process's procedural concurrent
    // assertions are cleared.
    FlushProceduralAssertionQueue(*current_process_);
    // §16.4.4: a flush point discards every pending report anyway, so any
    // specific-assertion cancellations recorded during the just-ended
    // activation are now moot; reset them so a later activation's reports are
    // not mistaken for the cancelled ones.
    current_process_->cancelled_deferred_labels.clear();
  }
}

uint64_t SimContext::CurrentDeferredReportGeneration() const {
  return current_process_ ? current_process_->deferred_report_generation : 0;
}

}  // namespace delta
