#include "simulator/sim_context.h"

#include "common/diagnostic.h"
#include "simulator/net.h"
#include "simulator/process.h"

namespace delta {

SimContext::SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
                       uint32_t seed)
    : scheduler_(sched), arena_(arena), diag_(diag), rng_(seed) {}

Variable* SimContext::FindVariable(std::string_view name) {
  auto* local = FindLocalVariable(name);
  if (local) return local;
  auto it = variables_.find(name);
  if (it != variables_.end()) return it->second;
  return nullptr;
}

Variable* SimContext::CreateVariable(std::string_view name, uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4Vec(arena_, width);
  // Initialize to X (bval=all-ones) per IEEE 1800-2023 §6.3.
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].bval = ~uint64_t{0};
  }
  variables_[name] = var;
  return var;
}

void SimContext::AliasVariable(std::string_view alias_name,
                               std::string_view target_name) {
  auto* target = FindVariable(target_name);
  if (target) variables_[alias_name] = target;
}

void SimContext::NullifyEventVariable(std::string_view name) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4Vec(arena_, 1);
  var->is_event = true;
  var->is_null_event = true;
  variables_[name] = var;
}

Net* SimContext::FindNet(std::string_view name) {
  auto it = nets_.find(name);
  return (it != nets_.end()) ? it->second : nullptr;
}

Net* SimContext::CreateNet(std::string_view name, NetType type, uint32_t width,
                           Strength charge_strength, uint64_t decay_ticks,
                           bool is_user_nettype,
                           std::string_view resolve_func) {
  auto* var = CreateVariable(name, width);
  if (is_user_nettype) {
    // §6.7.3: User-defined nettype defaults to data type default (x for logic).
    // CreateVariable already initializes to x, so nothing more needed.
  } else {
    // Initialize net value to z (aval=all-ones, bval=all-ones) per IEEE §6.5.
    for (uint32_t i = 0; i < var->value.nwords; ++i) {
      var->value.words[i].aval = ~uint64_t{0};
      var->value.words[i].bval = ~uint64_t{0};
    }
  }
  auto* net = arena_.Create<Net>();
  net->type = type;
  net->resolved = var;
  net->charge_strength = charge_strength;
  net->base_charge_strength = charge_strength;
  net->decay_ticks = decay_ticks;
  net->is_user_nettype = is_user_nettype;
  net->resolve_func = resolve_func;
  nets_[name] = net;
  return net;
}

void SimContext::RegisterFunction(std::string_view name, ModuleItem* item) {
  functions_[name] = item;
}

ModuleItem* SimContext::FindFunction(std::string_view name) {
  auto it = functions_.find(name);
  return (it != functions_.end()) ? it->second : nullptr;
}

void SimContext::RegisterLetDecl(std::string_view name, ModuleItem* item) {
  let_decls_[name] = item;
}

ModuleItem* SimContext::FindLetDecl(std::string_view name) {
  auto it = let_decls_.find(name);
  return (it != let_decls_.end()) ? it->second : nullptr;
}

void SimContext::PushScope() { scope_stack_.emplace_back(); }

void SimContext::PopScope() {
  if (!scope_stack_.empty()) scope_stack_.pop_back();
}

std::vector<std::unordered_map<std::string_view, Variable*>>
SimContext::SwapScopeStack(
    std::vector<std::unordered_map<std::string_view, Variable*>> new_stack) {
  auto old = std::move(scope_stack_);
  scope_stack_ = std::move(new_stack);
  return old;
}

void SimContext::PushStaticScope(std::string_view func_name) {
  scope_stack_.push_back(static_frames_[func_name]);
}

void SimContext::PopStaticScope(std::string_view func_name) {
  if (!scope_stack_.empty()) {
    static_frames_[func_name] = scope_stack_.back();
    scope_stack_.pop_back();
  }
}

Variable* SimContext::FindLocalVariable(std::string_view name) {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); ++it) {
    auto found = it->find(name);
    if (found != it->end()) return found->second;
  }
  return nullptr;
}

Variable* SimContext::CreateLocalVariable(std::string_view name,
                                          uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4VecVal(arena_, width, 0);
  if (!scope_stack_.empty()) {
    scope_stack_.back()[name] = var;
  }
  return var;
}

Variable* SimContext::FindStaticFuncVar(std::string_view func_name,
                                        std::string_view var_name) {
  auto it = static_frames_.find(func_name);
  if (it == static_frames_.end()) return nullptr;
  auto vit = it->second.find(var_name);
  if (vit == it->second.end()) return nullptr;
  return vit->second;
}

void SimContext::SaveStaticFuncVar(std::string_view func_name,
                                   std::string_view var_name, Variable* var) {
  static_frames_[func_name][var_name] = var;
}

void SimContext::AliasLocalVariable(std::string_view name, Variable* var) {
  if (!scope_stack_.empty()) {
    scope_stack_.back()[name] = var;
  }
}

void SimContext::PushQueueRefFrame() { queue_ref_stack_.emplace_back(); }

void SimContext::RecordQueueRef(const QueueRefBinding& binding) {
  if (!queue_ref_stack_.empty()) queue_ref_stack_.back().push_back(binding);
}

std::vector<QueueRefBinding> SimContext::PopQueueRefFrame() {
  if (queue_ref_stack_.empty()) return {};
  auto frame = std::move(queue_ref_stack_.back());
  queue_ref_stack_.pop_back();
  return frame;
}

void SimContext::RegisterFinalProcess(Process* proc) {
  final_processes_.push_back(proc);
}

void SimContext::AddSensitivity(std::string_view signal, Process* proc) {
  sensitivity_map_[std::string(signal)].push_back(proc);
}

const std::vector<Process*> SimContext::kEmptyProcessList;

const std::vector<Process*>& SimContext::GetSensitiveProcesses(
    std::string_view signal) const {
  auto it = sensitivity_map_.find(std::string(signal));
  return (it != sensitivity_map_.end()) ? it->second : kEmptyProcessList;
}

bool SimContext::IsReactiveContext() const {
  return current_process_ && current_process_->is_reactive;
}

void SimContext::RunFinalBlocks() {
  for (auto* proc : final_processes_) {
    proc->Resume();
  }
}

int32_t SimContext::Random32() { return static_cast<int32_t>(rng_()); }

uint32_t SimContext::Urandom32() { return static_cast<uint32_t>(rng_()); }

uint32_t SimContext::UrandomRange(uint32_t min_val, uint32_t max_val) {
  if (min_val > max_val) std::swap(min_val, max_val);
  std::uniform_int_distribution<uint32_t> dist(min_val, max_val);
  return dist(rng_);
}

void SimContext::AddPlusArg(std::string arg) {
  plus_args_.push_back(std::move(arg));
}

void SimContext::RegisterRealVariable(std::string_view name) {
  real_vars_.insert(name);
}

bool SimContext::IsRealVariable(std::string_view name) const {
  return real_vars_.count(name) != 0;
}

void SimContext::RegisterStringVariable(std::string_view name) {
  string_vars_.insert(name);
}

bool SimContext::IsStringVariable(std::string_view name) const {
  return string_vars_.count(name) != 0;
}

void SimContext::RegisterUnboundedParam(std::string_view name) {
  unbounded_params_.insert(name);
}

bool SimContext::IsUnboundedParam(std::string_view name) const {
  return unbounded_params_.count(name) != 0;
}

void SimContext::RegisterEnumType(std::string_view name,
                                  const EnumTypeInfo& info) {
  enum_types_[name] = info;
}

const EnumTypeInfo* SimContext::FindEnumType(std::string_view name) const {
  auto it = enum_types_.find(name);
  return (it != enum_types_.end()) ? &it->second : nullptr;
}

void SimContext::SetVariableEnumType(std::string_view var_name,
                                     std::string_view type_name) {
  var_enum_types_[var_name] = type_name;
}

const EnumTypeInfo* SimContext::GetVariableEnumType(
    std::string_view var_name) const {
  auto it = var_enum_types_.find(var_name);
  if (it == var_enum_types_.end()) return nullptr;
  return FindEnumType(it->second);
}

// --- §7.2: Struct type management ---

void SimContext::RegisterStructType(std::string_view name,
                                    const StructTypeInfo& info) {
  struct_types_[name] = info;
}

const StructTypeInfo* SimContext::FindStructType(std::string_view name) const {
  auto it = struct_types_.find(name);
  return (it != struct_types_.end()) ? &it->second : nullptr;
}

void SimContext::SetVariableStructType(std::string_view var_name,
                                       std::string_view type_name) {
  var_struct_types_[var_name] = type_name;
}

const StructTypeInfo* SimContext::GetVariableStructType(
    std::string_view var_name) const {
  auto it = var_struct_types_.find(var_name);
  if (it == var_struct_types_.end()) return nullptr;
  return FindStructType(it->second);
}

// --- §20.6.2: Type width registry ---

void SimContext::RegisterTypeWidth(std::string_view name, uint32_t width) {
  type_widths_[name] = width;
}

uint32_t SimContext::FindTypeWidth(std::string_view name) const {
  auto it = type_widths_.find(name);
  return (it != type_widths_.end()) ? it->second : 0;
}

// --- §7.4/§7.5/§7.10: Array metadata ---

void SimContext::RegisterArray(std::string_view name, const ArrayInfo& info) {
  array_infos_[name] = info;
}

ArrayInfo* SimContext::FindArrayInfo(std::string_view name) {
  auto it = array_infos_.find(name);
  return (it != array_infos_.end()) ? &it->second : nullptr;
}

const ArrayInfo* SimContext::FindArrayInfo(std::string_view name) const {
  auto it = array_infos_.find(name);
  return (it != array_infos_.end()) ? &it->second : nullptr;
}

// --- §7.10: Queue management ---

void QueueObject::AssignFreshIds() {
  element_ids.resize(elements.size());
  for (auto& id : element_ids) id = AllocateId();
}

QueueObject* SimContext::CreateQueue(std::string_view name, uint32_t elem_width,
                                     int32_t max_size) {
  auto* q = arena_.Create<QueueObject>();
  q->elem_width = elem_width;
  q->max_size = max_size;
  queues_[name] = q;
  return q;
}

QueueObject* SimContext::FindQueue(std::string_view name) {
  auto it = queues_.find(name);
  return (it != queues_.end()) ? it->second : nullptr;
}

// --- §7.8: Associative array management ---

uint32_t AssocArrayObject::Size() const {
  return static_cast<uint32_t>(is_string_key ? str_data.size()
                                             : int_data.size());
}

AssocArrayObject* SimContext::CreateAssocArray(std::string_view name,
                                               uint32_t elem_width,
                                               bool is_string_key,
                                               uint32_t index_width,
                                               bool is_wildcard,
                                               bool is_4state) {
  auto* aa = arena_.Create<AssocArrayObject>();
  aa->elem_width = elem_width;
  aa->is_string_key = is_string_key;
  aa->is_wildcard = is_wildcard;
  aa->index_width = index_width;
  aa->is_4state = is_4state;
  assoc_arrays_[name] = aa;
  return aa;
}

AssocArrayObject* SimContext::FindAssocArray(std::string_view name) {
  auto it = assoc_arrays_.find(name);
  return (it != assoc_arrays_.end()) ? it->second : nullptr;
}

// --- §7.3.2: Tagged union tag management ---

void SimContext::SetVariableTag(std::string_view var_name,
                                std::string_view tag) {
  var_tags_[var_name] = std::string(tag);
}

std::string_view SimContext::GetVariableTag(std::string_view var_name) const {
  auto it = var_tags_.find(var_name);
  if (it == var_tags_.end()) return {};
  return it->second;
}

int SimContext::OpenFile(std::string_view filename, std::string_view mode) {
  std::string fname(filename);
  std::string fmode(mode);
  FILE* fp = std::fopen(fname.c_str(), fmode.c_str());
  if (!fp) return 0;
  int fd = next_fd_++;
  file_descriptors_[fd] = fp;
  return fd;
}

void SimContext::CloseFile(int fd) {
  auto it = file_descriptors_.find(fd);
  if (it == file_descriptors_.end()) return;
  std::fclose(it->second);
  file_descriptors_.erase(it);
}

FILE* SimContext::GetFileHandle(int fd) {
  auto it = file_descriptors_.find(fd);
  return (it != file_descriptors_.end()) ? it->second : nullptr;
}

SemaphoreObject* SimContext::CreateSemaphore(std::string_view name,
                                             int32_t keys) {
  auto* sem = arena_.Create<SemaphoreObject>(keys);
  semaphores_[name] = sem;
  return sem;
}

SemaphoreObject* SimContext::FindSemaphore(std::string_view name) {
  auto it = semaphores_.find(name);
  return (it != semaphores_.end()) ? it->second : nullptr;
}

MailboxObject* SimContext::CreateMailbox(std::string_view name, int32_t bound) {
  auto* mb = arena_.Create<MailboxObject>(bound);
  mailboxes_[name] = mb;
  return mb;
}

MailboxObject* SimContext::FindMailbox(std::string_view name) {
  auto it = mailboxes_.find(name);
  return (it != mailboxes_.end()) ? it->second : nullptr;
}

void SimContext::SetEventTriggered(std::string_view name) {
  event_triggered_[name] = scheduler_.CurrentTime().ticks;
  // §15.5.5.1: Store on the Variable so merged aliases share triggered state.
  auto* var = FindVariable(name);
  if (var) var->triggered_ticks = scheduler_.CurrentTime().ticks;
}

bool SimContext::IsEventTriggered(std::string_view name) const {
  // §15.5.5.1: Check the Variable first so merged events share triggered state.
  auto vit = variables_.find(name);
  if (vit != variables_.end())
    return vit->second->triggered_ticks == scheduler_.CurrentTime().ticks;
  auto it = event_triggered_.find(name);
  if (it == event_triggered_.end()) return false;
  return it->second == scheduler_.CurrentTime().ticks;
}

// --- §8: Class type and object management ---

void SimContext::RegisterClassType(std::string_view name, ClassTypeInfo* info) {
  class_types_[name] = info;
}

ClassTypeInfo* SimContext::FindClassType(std::string_view name) {
  auto it = class_types_.find(name);
  return (it != class_types_.end()) ? it->second : nullptr;
}

void SimContext::SetVariableClassType(std::string_view var,
                                      std::string_view type) {
  var_class_types_[var] = type;
}

std::string_view SimContext::GetVariableClassType(std::string_view var) const {
  auto it = var_class_types_.find(var);
  return (it != var_class_types_.end()) ? it->second : std::string_view{};
}

void SimContext::SetVariableClassParamExprs(std::string_view var,
                                            std::vector<Expr*> exprs) {
  var_class_param_exprs_[var] = std::move(exprs);
}

static const std::vector<Expr*> kEmptyExprVec;

const std::vector<Expr*>& SimContext::GetVariableClassParamExprs(
    std::string_view var) const {
  auto it = var_class_param_exprs_.find(var);
  return (it != var_class_param_exprs_.end()) ? it->second : kEmptyExprVec;
}

uint64_t SimContext::AllocateClassObject(ClassObject* obj) {
  uint64_t id = next_handle_id_++;
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
  // §8.30.1: Object is weakly reachable if any weak reference points to it.
  for (const auto* wr : weak_references_) {
    if (wr->referent_handle == handle) return Reachability::kWeaklyReachable;
  }
  return Reachability::kUnreachable;
}

void SimContext::CollectGarbage() {
  if (class_objects_.empty()) return;

  // Phase 1: Mark handles directly referenced by live variables.
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

  // Objects on the this_stack_ are strongly reachable.
  std::unordered_set<ClassObject*> this_live;
  for (auto* obj : this_stack_) {
    if (obj) this_live.insert(obj);
  }

  // Phase 2: Transitively mark handles in properties of live objects.
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

  // Phase 3: Clear weak references to unreachable objects atomically.
  for (auto* wr : weak_references_) {
    if (wr->referent_handle != kNullClassHandle &&
        !live.count(wr->referent_handle)) {
      wr->Clear();
    }
  }

  // Phase 4: Sweep — deallocate unreachable objects.
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

// §12.4.2.1: Deferred violation reports.

void SimContext::AddPendingViolation(std::string msg) {
  if (current_process_) {
    current_process_->pending_violations.push_back(std::move(msg));
    // Schedule Observed region event to mature violations.
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
