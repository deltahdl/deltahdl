#include <algorithm>

#include "common/diagnostic.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

uint64_t SimContext::AllocateClassObject(ClassObject* obj) {
  uint64_t id = next_handle_id_++;
  // §18.14.1 object stability: seed the new object's RNG with the next random
  // value drawn from the active stream. While a thread is running this is the
  // creating thread's generator, so an object built with new inherits the next
  // value from that thread; with no thread current the draw comes from the
  // context-wide initialization RNG, covering objects created by a static
  // declaration initializer. Each object therefore receives its own stream.
  obj->rng_seed = DrawSeedForChild();
  class_objects_[id] = obj;
  obj->ref_count = 1;
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

void SimContext::CollectGarbage() {
  if (class_objects_.empty()) return;

  std::unordered_set<uint64_t> live;

  auto scan_var = [&](std::string_view name, Variable* var) {
    if (!var || !var_class_types_.count(name)) return;
    uint64_t h = var->value.ToUint64();
    if (h != kNullClassHandle) live.insert(h);
    if (var->has_pending_nba) {
      uint64_t ph = var->pending_nba.ToUint64();
      if (ph != kNullClassHandle) live.insert(ph);
    }
  };

  for (const auto& [name, var] : variables_) scan_var(name, var);
  for (const auto& scope : scope_stack_) {
    for (const auto& [name, var] : scope) scan_var(name, var);
  }
  for (const auto& [func, frame] : static_frames_) {
    for (const auto& [name, var] : frame) scan_var(name, var);
  }

  std::unordered_set<ClassObject*> this_live;
  for (auto* obj : this_stack_) {
    if (obj) this_live.insert(obj);
  }

  std::vector<uint64_t> worklist(live.begin(), live.end());
  while (!worklist.empty()) {
    uint64_t h = worklist.back();
    worklist.pop_back();
    auto it = class_objects_.find(h);
    if (it == class_objects_.end()) continue;
    for (const auto& [pname, pval] : it->second->properties) {
      uint64_t ph = pval.ToUint64();
      if (ph != kNullClassHandle && class_objects_.count(ph) &&
          !live.count(ph)) {
        live.insert(ph);
        worklist.push_back(ph);
      }
    }
  }

  for (auto* wr : weak_references_) {
    if (wr->referent_handle != kNullClassHandle &&
        !live.count(wr->referent_handle)) {
      wr->Clear();
    }
  }

  for (auto it = class_objects_.begin(); it != class_objects_.end();) {
    if (!live.count(it->first) && !this_live.count(it->second)) {
      it->second->ref_count = 0;
      it = class_objects_.erase(it);
    } else {
      ++it;
    }
  }
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

void SimContext::PopThis() {
  if (!this_stack_.empty()) this_stack_.pop_back();
}

ClassObject* SimContext::CurrentThis() const {
  return this_stack_.empty() ? nullptr : this_stack_.back();
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

void SimContext::AddPendingViolation(std::string msg) {
  if (current_process_) {
    current_process_->pending_violations.push_back(std::move(msg));

    auto* ev = scheduler_.GetEventPool().Acquire();
    Process* proc = current_process_;
    ev->callback = [this, proc]() {
      for (auto& v : proc->pending_violations) {
        diag_.Warning({}, std::move(v));
      }
      proc->pending_violations.clear();
    };
    scheduler_.ScheduleEvent(scheduler_.CurrentTime(), Region::kObserved, ev);
  } else {
    diag_.Warning({}, std::move(msg));
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
      diag_.Warning({}, std::move(v));
    }
    current_process_->pending_violations.clear();
  }
}

}  // namespace delta
