#include "simulation/sim_context.h"

#include "common/diagnostic.h"
#include "simulation/net.h"
#include "simulation/process.h"

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

Net* SimContext::FindNet(std::string_view name) {
  auto it = nets_.find(name);
  return (it != nets_.end()) ? it->second : nullptr;
}

Net* SimContext::CreateNet(std::string_view name, NetType type, uint32_t width,
                           Strength charge_strength, uint64_t decay_ticks) {
  auto* var = CreateVariable(name, width);
  // Initialize net value to z (aval=all-ones, bval=all-ones) per IEEE §6.5.
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].aval = ~uint64_t{0};
    var->value.words[i].bval = ~uint64_t{0};
  }
  auto* net = arena_.Create<Net>();
  net->type = type;
  net->resolved = var;
  net->charge_strength = charge_strength;
  net->decay_ticks = decay_ticks;
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

void SimContext::PushScope() { scope_stack_.emplace_back(); }

void SimContext::PopScope() {
  if (!scope_stack_.empty()) scope_stack_.pop_back();
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

void SimContext::AliasLocalVariable(std::string_view name, Variable* var) {
  if (!scope_stack_.empty()) {
    scope_stack_.back()[name] = var;
  }
}

void SimContext::RegisterFinalProcess(Process* proc) {
  final_processes_.push_back(proc);
}

void SimContext::AddSensitivity(std::string_view signal, Process* proc) {
  sensitivity_map_[signal].push_back(proc);
}

const std::vector<Process*> SimContext::kEmptyProcessList;

const std::vector<Process*>& SimContext::GetSensitiveProcesses(
    std::string_view signal) const {
  auto it = sensitivity_map_.find(signal);
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
}

bool SimContext::IsEventTriggered(std::string_view name) const {
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

uint64_t SimContext::AllocateClassObject(ClassObject* obj) {
  uint64_t id = next_handle_id_++;
  class_objects_[id] = obj;
  return id;
}

ClassObject* SimContext::GetClassObject(uint64_t handle) const {
  if (handle == kNullClassHandle) return nullptr;
  auto it = class_objects_.find(handle);
  return (it != class_objects_.end()) ? it->second : nullptr;
}

void SimContext::PushThis(ClassObject* obj) { this_stack_.push_back(obj); }

void SimContext::PopThis() {
  if (!this_stack_.empty()) this_stack_.pop_back();
}

ClassObject* SimContext::CurrentThis() const {
  return this_stack_.empty() ? nullptr : this_stack_.back();
}

}  // namespace delta
