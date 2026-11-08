#include "simulator/sim_context.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/coverage.h"
#include "simulator/covergroup_instance.h"
#include "simulator/dpi_runtime.h"
#include "simulator/exec_task.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"
#include "simulator/unit_scopes.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

SimContext::~SimContext() {
  g_park_slot = nullptr;
  if (dpi_runtime_ != nullptr && DpiForeignRuntime() == dpi_runtime_) {
    DpiSetForeignRuntime(nullptr);
  }
}

CoverageDB& SimContext::CoverageData() {
  if (coverage_db_ != nullptr) return *coverage_db_;
  if (!owned_coverage_db_) owned_coverage_db_ = std::make_unique<CoverageDB>();
  return *owned_coverage_db_;
}

CovergroupTable& SimContext::Covergroups() {
  if (!covergroups_) covergroups_ = std::make_unique<CovergroupTable>();
  return *covergroups_;
}

ClockingManager& SimContext::AcquireClockingManager() {
  if (clocking_mgr_ != nullptr) return *clocking_mgr_;
  if (owned_clocking_manager_ == nullptr) {
    owned_clocking_manager_ = std::make_unique<ClockingManager>();
  }
  clocking_mgr_ = owned_clocking_manager_.get();
  return *owned_clocking_manager_;
}

SpecifyManager& SimContext::AcquireSpecifyManager() {
  if (owned_specify_manager_ == nullptr) {
    owned_specify_manager_ = std::make_unique<SpecifyManager>();
  }
  specify_manager_ = owned_specify_manager_.get();
  return *owned_specify_manager_;
}

DpiRuntime& SimContext::AcquireDpiRuntime() {
  if (dpi_runtime_ != nullptr) {
    DpiSetForeignRuntime(dpi_runtime_);
    return *dpi_runtime_;
  }
  if (owned_dpi_runtime_ == nullptr) {
    owned_dpi_runtime_ = std::make_unique<DpiRuntime>();
  }
  dpi_runtime_ = owned_dpi_runtime_.get();
  DpiSetForeignRuntime(dpi_runtime_);
  return *owned_dpi_runtime_;
}

namespace {

struct SymbolTables {
  const std::unordered_map<std::string, std::string>& instance_types;
  const std::unordered_map<std::string_view, Variable*>& variables;
  const std::unordered_set<std::string>& top_modules;
};

struct NameLookup {
  std::string_view name;
  std::string_view head;
  std::string_view rest;
  const std::string& prefix;
};

void ShrinkInstancePrefix(std::string& p) {
  size_t last =
      (p.size() >= 2) ? p.find_last_of('.', p.size() - 2) : std::string::npos;
  if (last == std::string::npos) {
    p.clear();
  } else {
    p = p.substr(0, last + 1);
  }
}

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
  if (Variable* under_top = LookupRestUnderMatchingInstance(
          "", lookup.head, lookup.rest, tables)) {
    return under_top;
  }
  if (tables.top_modules.count(std::string(lookup.head)) == 0) return nullptr;
  auto top_it = tables.variables.find(lookup.rest);
  return (top_it != tables.variables.end()) ? top_it->second : nullptr;
}

Variable* FindUnderNamedScopes(
    const std::unordered_map<std::string_view, Variable*>& variables,
    const std::string& prefix, const std::vector<std::string_view>& scopes,
    std::string_view name) {
  if (name.find('.') == std::string_view::npos) return nullptr;
  for (size_t depth = scopes.size(); depth > 0; --depth) {
    for (size_t start = 0; start < depth; ++start) {
      std::string key = prefix;
      for (size_t i = start; i < depth; ++i) {
        key += scopes[i];
        key += '.';
      }
      key += name;
      auto it = variables.find(key);
      if (it != variables.end()) return it->second;
    }
  }
  return nullptr;
}

Variable* FindUnderInstanceOrNamedScopes(
    const std::unordered_map<std::string_view, Variable*>& variables,
    const std::string& prefix, const std::vector<std::string_view>& scopes,
    std::string_view name) {
  if (!prefix.empty()) {
    auto it = variables.find(prefix + std::string(name));
    if (it != variables.end()) return it->second;
  }
  return FindUnderNamedScopes(variables, prefix, scopes, name);
}

}  // namespace

Variable* SimContext::FindInGenerateBlock(const std::string& inst_prefix,
                                          std::string_view name) {
  if (!current_process_) return nullptr;
  for (const std::string& key :
       GenerateBlockKeys(inst_prefix, current_process_->gen_prefixes, name)) {
    auto found = variables_.find(key);
    if (found != variables_.end()) return found->second;
  }
  return nullptr;
}

void SimContext::SetDeferredArgSnapshot(const Expr* arg, const Logic4Vec& val) {
  deferred_arg_snapshots_[arg] = val;
}

const Logic4Vec* SimContext::FindDeferredArgSnapshot(const Expr* arg) const {
  auto it = deferred_arg_snapshots_.find(arg);
  if (it == deferred_arg_snapshots_.end()) return nullptr;
  return &it->second;
}

void SimContext::ClearDeferredArgSnapshot(const Expr* arg) {
  deferred_arg_snapshots_.erase(arg);
}

void SimContext::PushMethodClass(const ClassTypeInfo* cls) {
  method_class_stack_.push_back(cls);
}

void SimContext::PopMethodClass() {
  if (!method_class_stack_.empty()) method_class_stack_.pop_back();
}

const ClassTypeInfo* SimContext::CurrentMethodClass() const {
  return method_class_stack_.empty() ? nullptr : method_class_stack_.back();
}

Logic4Vec* SimContext::SetRsReturnSlot(Logic4Vec* slot) {
  Logic4Vec* prev = rs_return_slot_;
  rs_return_slot_ = slot;
  return prev;
}

const Logic4Vec* SimContext::MonitorLastValue(Variable* var) const {
  auto it = monitor_last_values_.find(var);
  return it == monitor_last_values_.end() ? nullptr : &it->second;
}

void SimContext::SetGlobalPrecision(TimeUnit u) {
  global_precision_ = u;
  if (!time_format_explicit_) {
    time_format_.units_number = static_cast<int>(u);
  }
}

void SimContext::SetLoweringInstancePrefix(std::string_view prefix) {
  lowering_inst_prefix_ = std::string(prefix);
}

std::string SimContext::ActiveInstancePrefix() const {
  if (prefix_override_.active) return prefix_override_.prefix;
  return current_process_ ? current_process_->inst_prefix
                          : lowering_inst_prefix_;
}

std::string SimContext::ActiveUnitScope() const {
  if (!units_.Separate()) return {};
  const Scope* frame = PackageFrame();
  if (frame != nullptr) return std::string(frame->package);
  return UnitScopes::ScopeName(units_.UnitOf(ActiveInstancePrefix()));
}

Variable* SimContext::FindInPackageScope(std::string_view name) {
  for (const std::string& key : PackageFrameKeys(name)) {
    auto found = variables_.find(key);
    if (found != variables_.end()) return found->second;
  }
  return nullptr;
}

ModuleItem* SimContext::FindFunctionInPackageScope(std::string_view name) {
  const Scope* frame = PackageFrame();
  if (frame == nullptr) return nullptr;
  for (const std::string& key : PackageScopedKeys(frame->package, name)) {
    std::string scoped = key;
    scoped.replace(scoped.find('.'), 1, "::");
    if (ModuleItem* func = FindFunction(scoped)) return func;
  }
  return nullptr;
}

Variable* SimContext::FindVariable(std::string_view name) {
  constexpr std::string_view kRootPrefix = "$root.";
  if (name.substr(0, kRootPrefix.size()) == kRootPrefix) {
    auto it =
        variables_.find(RootedStorageKey(name.substr(kRootPrefix.size())));
    if (it != variables_.end()) return it->second;
  }

  auto* local = FindLocalVariable(name);
  if (local) return local;
  if (auto* in_package = FindInPackageScope(name)) return in_package;
  if (Variable* from_root = FindUnitPathVariable(name)) return from_root;
  std::string prefix = ActiveInstancePrefix();

  if (auto* in_block = FindInGenerateBlock(prefix, name)) return in_block;

  if (auto* in_scope = FindUnderInstanceOrNamedScopes(
          variables_, prefix, ActiveNamedScopes(), name)) {
    return in_scope;
  }
  if (auto* outer = FindInNestedDeclOuterScopes(variables_, prefix, name))
    return outer;

  auto dot = name.find('.');
  if (prefix.empty() || dot != std::string_view::npos || IsImportedName(name)) {
    auto it = variables_.find(name);
    if (it != variables_.end()) return it->second;
  }

  if (dot == std::string_view::npos) return nullptr;
  std::string_view head = name.substr(0, dot);
  std::string_view rest = name.substr(dot + 1);
  NameLookup lookup{name, head, rest, prefix};
  SymbolTables tables{instance_types_, variables_, top_module_names_};
  return FindVariableByPrefixWalk(lookup, tables);
}

Variable* SimContext::CreateVariable(std::string_view name, uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4Vec(arena_, width);

  FillWithX(var->value);
  variables_[name] = var;
  return var;
}

void SimContext::AliasVariable(std::string_view alias_name,
                               std::string_view target_name) {
  auto* target = FindVariable(target_name);
  if (target) variables_[alias_name] = target;
}

void SimContext::AliasVariable(std::string_view alias_name, Variable* target) {
  if (target) variables_[alias_name] = target;
}

void SimContext::AliasNet(std::string_view alias_name,
                          std::string_view target_name) {
  auto* target = FindNet(target_name);
  if (target) nets_[alias_name] = target;
}

void SimContext::NullifyEventVariable(std::string_view name) {
  auto* var = FindVariable(name);
  if (var == nullptr) {
    var = arena_.Create<Variable>();
    var->value = MakeLogic4Vec(arena_, 1);
    var->is_event = true;
    variables_[name] = var;
    var->is_null_event = true;
    return;
  }
  int shared = 0;
  for (const auto& [key, value] : variables_) {
    if (value == var && ++shared > 1) break;
  }
  if (shared > 1) {
    auto* fresh = arena_.Create<Variable>();
    fresh->value = MakeLogic4Vec(arena_, 1);
    fresh->is_event = true;
    fresh->is_null_event = true;
    variables_[name] = fresh;
    return;
  }
  var->is_null_event = true;
}

namespace {

void InitNetDefaultValue(Variable* var, NetType type, bool is_user_nettype) {
  if (is_user_nettype) return;
  bool is_x = type == NetType::kTrireg;
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    uint64_t mask = WordMaskWithinWidth(var->value.width, i);
    var->value.words[i].aval = is_x ? mask : uint64_t{0};
    var->value.words[i].bval = mask;
  }
}

void PopulateNetFields(Net* net, Variable* var, NetType type,
                       const NetSpec& spec) {
  net->type = type;
  net->resolved = var;
  net->charge_strength = spec.charge_strength;
  net->base_charge_strength = spec.charge_strength;
  net->decay_ticks = spec.decay_ticks;
  net->decays = spec.decays;
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
  if (type == NetType::kTri0 || type == NetType::kTri1 ||
      type == NetType::kSupply0 || type == NetType::kSupply1 ||
      type == NetType::kTrireg) {
    net->Resolve(arena_);
  }
  return net;
}

void SimContext::SetCurrentProcess(Process* proc) {
  const bool kResuming =
      proc != nullptr && !proc->stand_in && scheduler_.HasRunThread(proc);
  if (proc == current_process_) {
    if (kResuming) GetGlobalVpiContext().NoteThreadEntered(proc);
    return;
  }
  if (proc == nullptr || !proc->stand_in) scheduler_.NoteThreadSwitch(proc);
  if (current_process_) {
    current_process_->saved_scope_stack = std::move(scope_stack_);
    current_process_->saved_named_scopes = std::move(active_scope_stack_);
    current_process_->saved_this_stack = std::move(this_stack_);
    current_process_->saved_method_class_stack = std::move(method_class_stack_);
  }
  if (proc) {
    scope_stack_ = std::move(proc->saved_scope_stack);
    active_scope_stack_ = std::move(proc->saved_named_scopes);
    this_stack_ = std::move(proc->saved_this_stack);
    method_class_stack_ = std::move(proc->saved_method_class_stack);
  } else {
    scope_stack_.clear();
    active_scope_stack_.clear();
    this_stack_.clear();
    method_class_stack_.clear();
  }
  current_process_ = proc;
  g_park_slot = proc != nullptr ? &proc->park : nullptr;
  if (proc != nullptr) proc->park.named_scopes = &active_scope_stack_;
  if (kResuming) GetGlobalVpiContext().NoteThreadEntered(proc);
}

void SimContext::CopyCarriedStacksTo(Process& child) const {
  child.saved_this_stack = this_stack_;
  child.saved_method_class_stack = method_class_stack_;
  child.saved_scope_stack = scope_stack_;
  if (!child.stand_in) scheduler_.NoteCarrier(&child);
}

void SimContext::ExitFunction() {
  if (function_depth_ > 0) --function_depth_;
}

void SimContext::SetDpiRuntime(DpiRuntime* dpi) {
  dpi_runtime_ = dpi;
  DpiSetForeignRuntime(dpi);
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

const std::vector<Process*> SimContext::kEmptyNamedScopeList;

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

void SimContext::RegisterOutermostScope(std::string_view name, Process* proc) {
  outermost_scope_map_[std::string(name)].push_back(proc);
}

const std::vector<Process*>& SimContext::FindOutermostScopeProcesses(
    std::string_view name) const {
  auto it = outermost_scope_map_.find(std::string(name));
  return (it != outermost_scope_map_.end()) ? it->second : kEmptyNamedScopeList;
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
      if (it == program_initials_by_block_.end()) return;
      auto& vec = it->second;
      auto pos = std::find(vec.begin(), vec.end(), proc);
      if (pos == vec.end()) return;
      vec.erase(pos);
    }
  }
  if (pending_program_initials_ > 0) {
    --pending_program_initials_;
    if (pending_program_initials_ == 0) programs_ended_ = true;
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
  if (pending_program_initials_ == 0) programs_ended_ = true;
}

void SimContext::RunFinalBlocks() {
  stop_requested_ = false;
  for (auto* proc : final_processes_) {
    SetCurrentProcess(proc);
    proc->Resume();
    if (stop_requested_) break;
  }
}

std::mt19937& SimContext::ActiveRng() {
  if (current_process_ != nullptr && !current_process_->is_static_init) {
    if (!current_process_->rng_initialized) {
      current_process_->rng.seed(current_process_->rng_seed);
      current_process_->rng_initialized = true;
    }
    return current_process_->rng;
  }
  return InitializationRng(ActiveInstancePrefix(), default_seed_);
}

uint32_t SimContext::DrawSeedForChild() {
  return static_cast<uint32_t>(ActiveRng()());
}

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
  InitializationRng(lowering_inst_prefix_, default_seed_).seed(seed);
}

uint32_t SimContext::UrandomRange(uint32_t min_val, uint32_t max_val) {
  if (min_val > max_val) std::swap(min_val, max_val);
  std::uniform_int_distribution<uint32_t> dist(min_val, max_val);
  return dist(ActiveRng());
}

void SimContext::AddPlusArg(std::string arg) {
  plus_args_.push_back(std::move(arg));
}

std::string SimContext::InstanceKeyOf(const std::string& cand) const {
  if (instance_types_.find(cand) != instance_types_.end()) return cand;
  if (std::string_view key = FindInterfacePortInstance(cand); !key.empty())
    return std::string(key);
  return std::string(FindInstanceKeyOfPath(cand));
}

std::string SimContext::ResolveInstanceScope(std::string_view ident) const {
  std::string prefix = ActiveInstancePrefix();
  std::string p = prefix;
  for (;;) {
    std::string cand = p + std::string(ident);
    if (std::string key = InstanceKeyOf(cand); !key.empty()) return key;
    if (p.empty()) break;
    size_t last =
        (p.size() >= 2) ? p.find_last_of('.', p.size() - 2) : std::string::npos;
    if (last == std::string::npos) {
      p.clear();
    } else {
      p = p.substr(0, last + 1);
    }
  }
  size_t dot = ident.find('.');
  if (dot != std::string_view::npos && IsTopModule(ident.substr(0, dot)))
    return InstanceKeyOf(std::string(ident.substr(dot + 1)));
  return {};
}

void SimContext::RegisterArray(std::string_view name, const ArrayInfo& info) {
  array_infos_[name] = info;
}

void SimContext::RegisterLocalArray(std::string_view name,
                                    const ArrayInfo& info) {
  scope_stack_.back().arrays[name] = arena_.Create<ArrayInfo>(info);
}

void SimContext::RegisterArrayInScope(std::string_view name,
                                      const ArrayInfo& info) {
  if (HasLocalScope()) {
    RegisterLocalArray(name, info);
    return;
  }
  RegisterArray(name, info);
}

void SimContext::RegisterStringVariable(std::string_view name) {
  if (auto* var = FindVariable(name)) var->is_string = true;
}

bool SimContext::IsStringVariable(std::string_view name) {
  const auto* var = FindVariable(name);
  return var != nullptr && var->is_string;
}

ArrayInfo* SimContext::FindArrayInfo(std::string_view name) {
  return const_cast<ArrayInfo*>(std::as_const(*this).FindArrayInfo(name));
}

const ArrayInfo* SimContext::FindArrayInfo(std::string_view name) const {
  constexpr std::string_view kRootPrefix = "$root.";
  if (name.starts_with(kRootPrefix)) {
    auto it =
        array_infos_.find(RootedStorageKey(name.substr(kRootPrefix.size())));
    return it == array_infos_.end() ? nullptr : &it->second;
  }
  for (auto frame = scope_stack_.crbegin(); frame != VisibleFramesEnd();
       ++frame) {
    auto local = frame->arrays.find(name);
    if (local != frame->arrays.end()) return local->second;
    if (frame->vars.count(name) != 0) return nullptr;
  }
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = array_infos_.find(key);
    if (it != array_infos_.end()) return &it->second;
  }
  return nullptr;
}

}  // namespace delta
