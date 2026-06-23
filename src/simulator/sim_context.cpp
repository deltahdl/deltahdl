#include "simulator/sim_context.h"

#include <algorithm>
#include <sstream>

#include "common/diagnostic.h"
#include "simulator/net.h"
#include "simulator/process.h"

namespace delta {

SimContext::SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
                       uint32_t seed)
    : scheduler_(sched), arena_(arena), diag_(diag), rng_(seed) {}

namespace {

// The two symbol tables consulted during a hierarchical name lookup: the map
// from instance path to its module type, and the flat variable table.
struct SymbolTables {
  const std::unordered_map<std::string, std::string>& instance_types;
  const std::unordered_map<std::string_view, Variable*>& variables;
};

// A hierarchical name being resolved: the full dotted `name`, plus its split
// into the leading instance segment (`head`) and the remainder (`rest`), and
// the `prefix` of the current scope from which the upward walk begins.
struct NameLookup {
  std::string_view name;
  std::string_view head;
  std::string_view rest;
  const std::string& prefix;
};

// Shrinks `p` to the next-shorter dotted instance prefix (dropping the final
// path segment, keeping the trailing dot), clearing it when no segment remains.
void ShrinkInstancePrefix(std::string& p) {
  size_t last =
      (p.size() >= 2) ? p.find_last_of('.', p.size() - 2) : std::string::npos;
  if (last == std::string::npos) {
    p.clear();
  } else {
    p = p.substr(0, last + 1);
  }
}

// When the instance at `p` has type `head`, looks up `rest` under that prefix.
// Returns the matching variable or nullptr.
Variable* LookupRestUnderMatchingInstance(const std::string& p,
                                          std::string_view head,
                                          std::string_view rest,
                                          const SymbolTables& tables) {
  std::string prefix_no_dot = p;
  if (!prefix_no_dot.empty() && prefix_no_dot.back() == '.')
    prefix_no_dot.pop_back();
  auto type_it = tables.instance_types.find(prefix_no_dot);
  if (type_it == tables.instance_types.end() || type_it->second != head)
    return nullptr;
  std::string cand = p + std::string(rest);
  auto cit = tables.variables.find(cand);
  return (cit != tables.variables.end()) ? cit->second : nullptr;
}

// Walks progressively shorter instance prefixes searching for `name` (or its
// rest under a matching instance head) in the variable table. Extracted from
// FindVariable so the lookup body stays a single cohesive step.
Variable* FindVariableByPrefixWalk(const NameLookup& lookup,
                                   const SymbolTables& tables) {
  std::string p = lookup.prefix;
  while (!p.empty()) {
    ShrinkInstancePrefix(p);
    Variable* under_inst =
        LookupRestUnderMatchingInstance(p, lookup.head, lookup.rest, tables);
    if (under_inst) return under_inst;
    std::string cand = p + std::string(lookup.name);
    auto cit = tables.variables.find(cand);
    if (cit != tables.variables.end()) return cit->second;
  }
  return nullptr;
}

}  // namespace

Variable* SimContext::FindVariable(std::string_view name) {
  auto* local = FindLocalVariable(name);
  if (local) return local;
  std::string prefix;
  if (current_process_) prefix = current_process_->inst_prefix;

  if (!prefix.empty()) {
    std::string prefixed = prefix + std::string(name);
    auto it = variables_.find(prefixed);
    if (it != variables_.end()) return it->second;
  }
  auto it = variables_.find(name);
  if (it != variables_.end()) return it->second;

  auto dot = name.find('.');
  if (dot == std::string_view::npos) return nullptr;
  std::string_view head = name.substr(0, dot);
  std::string_view rest = name.substr(dot + 1);
  NameLookup lookup{name, head, rest, prefix};
  SymbolTables tables{instance_types_, variables_};
  return FindVariableByPrefixWalk(lookup, tables);
}

Variable* SimContext::CreateVariable(std::string_view name, uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4Vec(arena_, width);

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

namespace {

// §6.7.1: install a net's default value before it is driven. A user-defined
// nettype keeps the variable's existing initialization; a trireg defaults to x
// (it holds charge, unknown until driven); every other net defaults to z.
void InitNetDefaultValue(Variable* var, NetType type, bool is_user_nettype) {
  if (is_user_nettype) {
  } else if (type == NetType::kTrireg) {
    // Encode x as aval=0, bval=1 per bit.
    for (uint32_t i = 0; i < var->value.nwords; ++i) {
      var->value.words[i].aval = uint64_t{0};
      var->value.words[i].bval = ~uint64_t{0};
    }
  } else {
    // z (high impedance) until driven.
    for (uint32_t i = 0; i < var->value.nwords; ++i) {
      var->value.words[i].aval = ~uint64_t{0};
      var->value.words[i].bval = ~uint64_t{0};
    }
  }
}

// Populates a freshly created Net's fields from the CreateNet arguments
// (§6.7.1: nettype, charge strength/decay, user-nettype flag, resolve func).
void PopulateNetFields(Net* net, Variable* var, NetType type,
                       const NetSpec& spec) {
  net->type = type;
  net->resolved = var;
  net->charge_strength = spec.charge_strength;
  net->base_charge_strength = spec.charge_strength;
  net->decay_ticks = spec.decay_ticks;
  net->is_user_nettype = spec.is_user_nettype;
  net->resolve_func = spec.resolve_func;
}

}  // namespace

Net* SimContext::CreateNet(std::string_view name, NetType type, uint32_t width,
                           const NetSpec& spec) {
  auto* var = CreateVariable(name, width);
  if (spec.is_signed) var->is_signed = true;
  InitNetDefaultValue(var, type, spec.is_user_nettype);
  auto* net = arena_.Create<Net>();
  PopulateNetFields(net, var, type, spec);
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

void SimContext::RegisterSequenceDecl(std::string_view name, ModuleItem* item) {
  sequence_decls_[name] = item;
}

ModuleItem* SimContext::FindSequenceDecl(std::string_view name) {
  auto it = sequence_decls_.find(name);
  return (it != sequence_decls_.end()) ? it->second : nullptr;
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

std::string_view SimContext::StaticFrameKey(std::string_view name) {
  if (!current_process_ || current_process_->inst_prefix.empty()) return name;
  auto* key = arena_.Create<std::string>(current_process_->inst_prefix +
                                         std::string(name));
  return *key;
}

void SimContext::PushStaticScope(std::string_view func_name) {
  scope_stack_.push_back(static_frames_[StaticFrameKey(func_name)]);
}

void SimContext::PopStaticScope(std::string_view func_name) {
  if (!scope_stack_.empty()) {
    static_frames_[StaticFrameKey(func_name)] = scope_stack_.back();
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
  auto it = static_frames_.find(StaticFrameKey(func_name));
  if (it == static_frames_.end()) return nullptr;
  auto vit = it->second.find(var_name);
  if (vit == it->second.end()) return nullptr;
  return vit->second;
}

void SimContext::SaveStaticFuncVar(std::string_view func_name,
                                   std::string_view var_name, Variable* var) {
  static_frames_[StaticFrameKey(func_name)][var_name] = var;
}

void SimContext::AliasLocalVariable(std::string_view name, Variable* var) {
  if (!scope_stack_.empty()) {
    scope_stack_.back()[name] = var;
  }
}

void SimContext::PushFuncName(std::string_view name) {
  func_name_stack_.push_back(name);
}

void SimContext::PopFuncName() {
  if (!func_name_stack_.empty()) func_name_stack_.pop_back();
}

std::string_view SimContext::CurrentFuncName() const {
  return func_name_stack_.empty() ? std::string_view{}
                                  : func_name_stack_.back();
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

void SimContext::PushAssocRefFrame() { assoc_ref_stack_.emplace_back(); }

void SimContext::RecordAssocRef(const AssocRefBinding& binding) {
  if (!assoc_ref_stack_.empty()) assoc_ref_stack_.back().push_back(binding);
}

std::vector<AssocRefBinding> SimContext::PopAssocRefFrame() {
  if (assoc_ref_stack_.empty()) return {};
  auto frame = std::move(assoc_ref_stack_.back());
  assoc_ref_stack_.pop_back();
  return frame;
}

void SimContext::RegisterFinalProcess(Process* proc) {
  final_processes_.push_back(proc);
}

void SimContext::AddSensitivity(std::string_view signal, Process* proc) {
  sensitivity_map_[std::string(signal)].push_back(proc);
}

const std::vector<Process*> SimContext::kEmptyProcessList;
const std::vector<Process*> SimContext::kEmptyNamedScopeList;

const std::vector<Process*>& SimContext::GetSensitiveProcesses(
    std::string_view signal) const {
  auto it = sensitivity_map_.find(std::string(signal));
  return (it != sensitivity_map_.end()) ? it->second : kEmptyProcessList;
}

bool SimContext::IsReactiveContext() const {
  return current_process_ && current_process_->is_reactive;
}

void SimContext::RegisterNamedScope(std::string_view name, Process* proc) {
  named_scope_map_[std::string(name)].push_back(proc);
}

void SimContext::UnregisterNamedScope(std::string_view name, Process* proc) {
  auto it = named_scope_map_.find(std::string(name));
  if (it == named_scope_map_.end()) return;
  auto& vec = it->second;
  vec.erase(std::remove(vec.begin(), vec.end(), proc), vec.end());
}

const std::vector<Process*>& SimContext::FindNamedScopeProcesses(
    std::string_view name) const {
  auto it = named_scope_map_.find(std::string(name));
  return (it != named_scope_map_.end()) ? it->second : kEmptyNamedScopeList;
}

static void KillDescendants(Process* proc) {
  for (auto* child : proc->children) {
    child->active = false;
    KillDescendants(child);
  }
}

void SimContext::RegisterProgramInitial(uint32_t program_block_id,
                                        Process* proc) {
  ++pending_program_initials_;
  if (proc && program_block_id != 0) {
    proc->program_block_id = program_block_id;
    program_initials_by_block_[program_block_id].push_back(proc);
  }
}

void SimContext::OnProgramInitialComplete(Process* proc) {
  if (proc) {
    KillDescendants(proc);
    if (proc->program_block_id != 0) {
      auto it = program_initials_by_block_.find(proc->program_block_id);
      if (it != program_initials_by_block_.end()) {
        auto& vec = it->second;
        vec.erase(std::remove(vec.begin(), vec.end(), proc), vec.end());
      }
    }
  }
  if (pending_program_initials_ > 0) {
    --pending_program_initials_;
    if (pending_program_initials_ == 0) stop_requested_ = true;
  }
}

void SimContext::ExitProgramBlock(uint32_t program_block_id) {
  if (program_block_id == 0) return;
  auto it = program_initials_by_block_.find(program_block_id);
  if (it == program_initials_by_block_.end()) return;
  auto procs = std::move(it->second);
  it->second.clear();
  for (auto* proc : procs) {
    if (!proc) continue;
    KillDescendants(proc);
    proc->active = false;
    if (pending_program_initials_ > 0) --pending_program_initials_;
  }
  if (pending_program_initials_ == 0) stop_requested_ = true;
}

void SimContext::RunFinalBlocks() {
  stop_requested_ = false;
  for (auto* proc : final_processes_) {
    proc->Resume();
    if (stop_requested_) break;
  }
}

std::mt19937& SimContext::ActiveRng() {
  // §18.14.2 thread stability: when a thread is running, every randomization
  // draw made from it must come from that thread's own generator so it stays
  // independent of sibling execution order. The hierarchical seed is
  // installed once, on first use, by drawing the next value from the parent's
  // active stream (which is whatever generator the current process inherits).
  if (current_process_ != nullptr) {
    if (!current_process_->rng_initialized) {
      current_process_->rng.seed(current_process_->rng_seed);
      current_process_->rng_initialized = true;
    }
    return current_process_->rng;
  }
  return rng_;
}

uint32_t SimContext::DrawSeedForChild() {
  return static_cast<uint32_t>(ActiveRng()());
}

std::mt19937& SimContext::ObjectRng(ClassObject* obj) {
  // §18.14.3 object stability: return the object's own stream so its
  // randomization is independent of every other object and of the context-wide
  // ($random/$urandom) and per-thread generators. Seed lazily the first time
  // the stream is touched, from the value installed at allocation time, so a
  // sequence of draws replays from the same starting state.
  if (!obj->rng_initialized) {
    obj->rng.seed(obj->rng_seed);
    obj->rng_initialized = true;
  }
  return obj->rng;
}

void SimContext::SeedObjectRng(ClassObject* obj, uint32_t seed) {
  // §18.14.3: srandom() may reseed an object's RNG at any time. Reset both the
  // recorded seed and the live stream so subsequent draws replay the sequence
  // keyed by `seed`, regardless of any draws already taken.
  obj->rng_seed = seed;
  obj->rng.seed(seed);
  obj->rng_initialized = true;
}

std::string SimContext::GetRandState(ClassObject* obj) {
  // §18.13.4: retrieve the object's current RNG internal state. ObjectRng
  // materializes the stream lazily, so the state reported reflects whatever the
  // object would next draw from. Streaming the generator out captures its full
  // state without consuming any value.
  std::ostringstream os;
  os << ObjectRng(obj);
  return os.str();
}

std::string SimContext::GetRandState(Process* proc) {
  // §18.13.4: retrieve the current RNG internal state of a process. Mirror the
  // lazy seeding the active-stream path uses so a process that has not yet
  // drawn still reports the state keyed by its installed seed rather than a
  // default generator.
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::ostringstream os;
  os << proc->rng;
  return os.str();
}

void SimContext::SetRandState(ClassObject* obj, const std::string& state) {
  // §18.13.5: set the object's RNG internal state from `state`. ObjectRng
  // materializes the stream lazily, so touch it first to guarantee the
  // generator exists, then deserialize over it. mt19937's operator>> restores
  // the complete state, so a value produced by GetRandState replays from the
  // exact position it was captured. Mark the stream initialized so a later
  // ObjectRng() does not reseed from the recorded seed and discard the restore.
  std::mt19937& gen = ObjectRng(obj);
  std::istringstream is(state);
  is >> gen;
  obj->rng_initialized = true;
}

void SimContext::SetRandState(Process* proc, const std::string& state) {
  // §18.13.5: set the process RNG internal state from `state`, mirroring the
  // object path. Ensure the stream is live before deserializing so the restore
  // is not later overwritten by the lazy seed-on-first-use step.
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::istringstream is(state);
  is >> proc->rng;
}

int32_t SimContext::Random32() { return static_cast<int32_t>(ActiveRng()()); }

uint32_t SimContext::Urandom32() {
  return static_cast<uint32_t>(ActiveRng()());
}

void SimContext::SeedUrandom(uint32_t seed) {
  if (current_process_ != nullptr) {
    current_process_->rng_seed = seed;
    current_process_->rng.seed(seed);
    current_process_->rng_initialized = true;
    return;
  }
  rng_.seed(seed);
}

uint32_t SimContext::UrandomRange(uint32_t min_val, uint32_t max_val) {
  if (min_val > max_val) std::swap(min_val, max_val);
  std::uniform_int_distribution<uint32_t> dist(min_val, max_val);
  return dist(ActiveRng());
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

void SimContext::RegisterTypeWidth(std::string_view name, uint32_t width) {
  type_widths_[name] = width;
}

uint32_t SimContext::FindTypeWidth(std::string_view name) const {
  auto it = type_widths_.find(name);
  return (it != type_widths_.end()) ? it->second : 0;
}

void SimContext::RegisterInstanceType(std::string_view prefix,
                                      std::string_view type) {
  instance_types_[std::string(prefix)] = std::string(type);
}

std::string_view SimContext::FindInstanceType(std::string_view prefix) const {
  auto it = instance_types_.find(std::string(prefix));
  return (it != instance_types_.end()) ? std::string_view(it->second)
                                       : std::string_view{};
}

void SimContext::RegisterInstanceBinding(std::string_view prefix,
                                         std::string_view library,
                                         std::string_view cell) {
  // §33.7: store the binding already joined as "library.cell" so the display
  // path can hand it straight back without re-formatting on every %l.
  instance_bindings_[std::string(prefix)] =
      std::string(library) + "." + std::string(cell);
}

std::string_view SimContext::FindInstanceBinding(
    std::string_view prefix) const {
  auto it = instance_bindings_.find(std::string(prefix));
  return (it != instance_bindings_.end()) ? std::string_view(it->second)
                                          : std::string_view{};
}

void SimContext::RegisterVirtualInterfaceVar(const Variable* v) {
  if (v) vi_vars_.insert(v);
}

bool SimContext::IsVirtualInterfaceVar(const Variable* v) const {
  return v && vi_vars_.count(v) != 0;
}

void SimContext::BindVirtualInterface(const Variable* v,
                                      std::string_view scope) {
  if (v) vi_bindings_[v] = std::string(scope);
}

void SimContext::UnbindVirtualInterface(const Variable* v) {
  vi_bindings_.erase(v);
}

bool SimContext::VirtualInterfaceIsBound(const Variable* v) const {
  return vi_bindings_.find(v) != vi_bindings_.end();
}

std::string_view SimContext::VirtualInterfaceBinding(const Variable* v) const {
  auto it = vi_bindings_.find(v);
  return (it != vi_bindings_.end()) ? std::string_view(it->second)
                                    : std::string_view{};
}

std::string SimContext::ResolveInstanceScope(std::string_view ident) const {
  std::string prefix;
  if (current_process_) prefix = current_process_->inst_prefix;
  // Walk progressively shorter instance prefixes, mirroring FindVariable, so a
  // bare instance name resolves to its full hierarchical scope.
  std::string p = prefix;
  for (;;) {
    std::string cand = p + std::string(ident);
    if (instance_types_.find(cand) != instance_types_.end()) return cand;
    if (p.empty()) break;
    size_t last =
        (p.size() >= 2) ? p.find_last_of('.', p.size() - 2) : std::string::npos;
    if (last == std::string::npos) {
      p.clear();
    } else {
      p = p.substr(0, last + 1);
    }
  }
  return {};
}

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

void QueueObject::AssignFreshIds() {
  element_ids.resize(elements.size());
  for (auto& id : element_ids) id = AllocateId();
}

QueueObject* SimContext::CreateQueue(std::string_view name, uint32_t elem_width,
                                     int32_t max_size, bool is_4state) {
  auto* q = arena_.Create<QueueObject>();
  q->elem_width = elem_width;
  q->is_4state = is_4state;
  q->max_size = max_size;
  queues_[name] = q;
  return q;
}

QueueObject* SimContext::FindQueue(std::string_view name) {
  auto it = queues_.find(name);
  return (it != queues_.end()) ? it->second : nullptr;
}

uint32_t AssocArrayObject::Size() const {
  return static_cast<uint32_t>(is_string_key ? str_data.size()
                                             : int_data.size());
}

namespace {

// Populates a freshly created AssocArrayObject's fields from the
// CreateAssocArray arguments (§7.8: element shape + index type).
void PopulateAssocArrayFields(AssocArrayObject* aa, uint32_t elem_width,
                              bool is_string_key, const AssocArraySpec& spec) {
  aa->elem_width = elem_width;
  aa->is_string_key = is_string_key;
  aa->is_wildcard = spec.is_wildcard;
  aa->index_width = spec.index_width;
  aa->is_4state = spec.is_4state;
  aa->is_index_signed = spec.is_index_signed;
}

}  // namespace

AssocArrayObject* SimContext::CreateAssocArray(std::string_view name,
                                               uint32_t elem_width,
                                               bool is_string_key,
                                               const AssocArraySpec& spec) {
  auto* aa = arena_.Create<AssocArrayObject>();
  PopulateAssocArrayFields(aa, elem_width, is_string_key, spec);
  assoc_arrays_[name] = aa;
  return aa;
}

AssocArrayObject* SimContext::FindAssocArray(std::string_view name) {
  auto it = assoc_arrays_.find(name);
  return (it != assoc_arrays_.end()) ? it->second : nullptr;
}

void SimContext::SetVariableTag(std::string_view var_name,
                                std::string_view tag) {
  var_tags_[var_name] = std::string(tag);
}

std::string_view SimContext::GetVariableTag(std::string_view var_name) const {
  auto it = var_tags_.find(var_name);
  if (it == var_tags_.end()) return {};
  return it->second;
}

void SimContext::EnsureStdioDescriptors() {
  if (stdio_descriptors_ready_) return;
  stdio_descriptors_ready_ = true;
  // STDIN/STDOUT/STDERR are pre-opened by §21.3.1 at the reserved fd values.
  // Channel 0 of an mcd points at the standard output (§21.3.1, LSB rule).
  file_descriptors_[kStdinFd] = stdin;
  file_descriptors_[kStdoutFd] = stdout;
  file_descriptors_[kStderrFd] = stderr;
  mcd_channels_[0] = stdout;
}

uint32_t SimContext::OpenFile(std::string_view filename,
                              std::string_view mode) {
  EnsureStdioDescriptors();
  std::string fname(filename);
  std::string fmode(mode);
  FILE* fp = std::fopen(fname.c_str(), fmode.c_str());
  if (!fp) return 0;
  // Lowest free slot in 3..0x7FFFFFFF, so $fopen reuses channels closed earlier
  // (§21.3.1).
  uint32_t slot = 3;
  while (file_descriptors_.count(kFdMsb | slot) != 0) ++slot;
  uint32_t fd = kFdMsb | slot;
  file_descriptors_[fd] = fp;
  // §21.3.4: only the "r"/"r+" type families authorize reading. Every such
  // type string begins with 'r', so track readability by that leading letter.
  if (!fmode.empty() && fmode.front() == 'r') readable_fds_.insert(fd);
  return fd;
}

uint32_t SimContext::OpenMcd(std::string_view filename) {
  EnsureStdioDescriptors();
  // mcd LSB (bit 0) is reserved for stdout; MSB (bit 31) must remain clear.
  // §21.3.1 limits an implementation to channels 1..30 for output files.
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if (mcd_channels_[bit] == nullptr) {
      std::string fname(filename);
      FILE* fp = std::fopen(fname.c_str(), "w");
      if (!fp) return 0;
      mcd_channels_[bit] = fp;
      return uint32_t{1} << bit;
    }
  }
  return 0;
}

void SimContext::CloseFile(uint32_t descriptor) {
  EnsureStdioDescriptors();
  if ((descriptor & kFdMsb) != 0) {
    // STDIN/STDOUT/STDERR are not closable per §21.3.1.
    if (descriptor == kStdinFd || descriptor == kStdoutFd ||
        descriptor == kStderrFd) {
      return;
    }
    auto it = file_descriptors_.find(descriptor);
    if (it == file_descriptors_.end()) return;
    std::fclose(it->second);
    file_descriptors_.erase(it);
    readable_fds_.erase(descriptor);
    return;
  }
  // Multichannel descriptor: every bit set selects a channel to close.
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if ((descriptor & (uint32_t{1} << bit)) == 0) continue;
    if (mcd_channels_[bit] == nullptr) continue;
    std::fclose(mcd_channels_[bit]);
    mcd_channels_[bit] = nullptr;
  }
}

FILE* SimContext::GetFileHandle(uint32_t fd) {
  EnsureStdioDescriptors();
  auto it = file_descriptors_.find(fd);
  return (it != file_descriptors_.end()) ? it->second : nullptr;
}

bool SimContext::IsFdReadable(uint32_t fd) const {
  // §21.3.4: STDIN is pre-opened for reading; STDOUT/STDERR are append-only.
  if (fd == kStdinFd) return true;
  if (fd == kStdoutFd || fd == kStderrFd) return false;
  return readable_fds_.count(fd) != 0;
}

std::vector<FILE*> SimContext::GetMcdFiles(uint32_t mcd) {
  EnsureStdioDescriptors();
  std::vector<FILE*> result;
  for (uint32_t bit = 0; bit < 31; ++bit) {
    if ((mcd & (uint32_t{1} << bit)) == 0) continue;
    if (mcd_channels_[bit] != nullptr) result.push_back(mcd_channels_[bit]);
  }
  return result;
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

  auto* var = FindVariable(name);
  if (var) var->triggered_ticks = scheduler_.CurrentTime().ticks;
}

bool SimContext::IsEventTriggered(std::string_view name) const {
  auto vit = variables_.find(name);
  if (vit != variables_.end())
    return vit->second->triggered_ticks == scheduler_.CurrentTime().ticks;
  auto it = event_triggered_.find(name);
  if (it == event_triggered_.end()) return false;
  return it->second == scheduler_.CurrentTime().ticks;
}

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

}  // namespace delta
