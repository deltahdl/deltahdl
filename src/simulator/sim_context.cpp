#include "simulator/sim_context.h"

#include <algorithm>
#include <memory>
#include <random>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "simulator/coverage.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/specify.h"

namespace delta {

// Defined here, where CoverageDB is a complete type, so the owning unique_ptr
// member can be destroyed.
SimContext::~SimContext() = default;

CoverageDB& SimContext::CoverageData() {
  // §19.9: an externally injected database wins; otherwise create the run's own
  // and reuse it on every later call so the coverage system tasks/functions all
  // see the same live data.
  if (coverage_db_ != nullptr) return *coverage_db_;
  if (!owned_coverage_db_) owned_coverage_db_ = std::make_unique<CoverageDB>();
  return *owned_coverage_db_;
}

SpecifyManager& SimContext::AcquireSpecifyManager() {
  if (owned_specify_manager_ == nullptr) {
    owned_specify_manager_ = std::make_unique<SpecifyManager>();
  }
  specify_manager_ = owned_specify_manager_.get();
  return *owned_specify_manager_;
}

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
  // §23.6: a hierarchical name rooted at the top module (e.g. "top.sig") strips
  // its leading segment against the top instance, which is keyed under the
  // empty prefix. The walk above skips that iteration when it starts from an
  // empty prefix (a top-level process or a test-time lookup), so try it
  // explicitly.
  return LookupRestUnderMatchingInstance("", lookup.head, lookup.rest, tables);
}

}  // namespace

// §27.4: resolves `name` against the generate block instances the running
// process is in, if it is in any. `inst_prefix` is the process's
// module-instance prefix, which the block prefixes sit inside. Returns nullptr
// when there is no enclosing generate block or none of them declares such a
// name, leaving the caller to carry on with the enclosing scopes.
//
// The blocks are tried innermost first because §23.9 rules that "If it is
// declared locally, then the local item shall be used; if not, the search shall
// continue upward until an item by that name is found or until a module,
// interface, program, or checker boundary is encountered".
// Process::gen_prefixes holds them outermost first, so the walk runs backwards
// over it.
Variable* SimContext::FindInGenerateBlock(const std::string& inst_prefix,
                                          std::string_view name) {
  if (!current_process_) return nullptr;
  const std::vector<std::string>& prefixes = current_process_->gen_prefixes;
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    auto found = variables_.find(inst_prefix + *it + std::string(name));
    if (found != variables_.end()) return found->second;
  }
  return nullptr;
}

bool SimContext::AssertCheckingEnabled(uint32_t type_bit,
                                       uint32_t directive_bit) const {
  if (!assert_checking_off_) return true;
  return (assert_checking_off_atype_ & type_bit) == 0 ||
         (assert_checking_off_dtype_ & directive_bit) == 0;
}

const Logic4Vec* SimContext::FindDeferredArgSnapshot(const Expr* arg) const {
  auto it = deferred_arg_snapshots_.find(arg);
  if (it == deferred_arg_snapshots_.end()) return nullptr;
  return &it->second;
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
  // §32.4.3's rebuild stands in the instance that declared what is being
  // rebuilt, which is neither of the two below.
  if (prefix_override_.active) return prefix_override_.prefix;
  return current_process_ ? current_process_->inst_prefix
                          : lowering_inst_prefix_;
}

Variable* SimContext::FindVariable(std::string_view name) {
  // §23.6: "The instance name $root refers to the top of the instantiated
  // design and is used to unambiguously gain access to the top of the design."
  // A name written from there is absolute, so it is read straight out of
  // variables_ and never joined to ActiveInstancePrefix(), which would make
  // the top of the design relative to whichever instance is running. `$root`
  // cannot spell a local or a prefixed name either, `$` starting no
  // identifier, so this stands ahead of both lookups below.
  //
  // variables_ keys a top-level hierarchy block's own declarations under no
  // instance prefix, so the remainder after "$root." is the key itself.
  constexpr std::string_view kRootPrefix = "$root.";
  if (name.substr(0, kRootPrefix.size()) == kRootPrefix) {
    auto it = variables_.find(name.substr(kRootPrefix.size()));
    if (it != variables_.end()) return it->second;
  }

  auto* local = FindLocalVariable(name);
  if (local) return local;
  std::string prefix = ActiveInstancePrefix();

  // §27.4: a generate block is a separate scope, and its declarations are
  // stored under the block instance's prefix. The innermost scope is searched
  // first, so a name that the block declares resolves to that declaration
  // ahead of a like-named one in the enclosing module.
  if (auto* in_block = FindInGenerateBlock(prefix, name)) return in_block;

  if (!prefix.empty()) {
    std::string prefixed = prefix + std::string(name);
    auto it = variables_.find(prefixed);
    if (it != variables_.end()) return it->second;
  }

  auto dot = name.find('.');
  // §23.9: the upward search "shall continue upward until an item by that name
  // is found or until a module, interface, program, or checker boundary is
  // encountered. If the item is a variable, it shall stop at a module
  // boundary". The bare key is the enclosing scope's, so reading it from
  // inside an instance is that forbidden step. It stays the answer in the
  // three cases §23.9 does not forbid: with no instance prefix in force it is
  // the ordinary lookup rather than an upward step; a dotted name is the §23.8
  // climb, which names the module it reaches; and a name a package import
  // brought into scope is bound flat under its unqualified spelling rather
  // than declared in an enclosing module at all. §23.4 adds a fourth: a module
  // declared inside the one instantiating it, of which that subclause says
  // "The outer name space is visible to the inner module so that any name
  // declared there can be used", so the boundary §23.9 draws is not there.
  // §23.6's `$root` is a fifth, answered above rather than here: it names the
  // top of the design outright rather than climbing to it, so no boundary
  // stands between the reference and what it reaches.
  if (prefix.empty() || dot != std::string_view::npos ||
      imported_names_.count(name) != 0 ||
      nested_decl_scopes_.count(std::string(prefix)) != 0) {
    auto it = variables_.find(name);
    if (it != variables_.end()) return it->second;
  }

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

  // §6.4: an uninitialized 4-state variable defaults to x. Canonical
  // Convention A encodes x as (aval=1, bval=1) per bit. Only the bits inside
  // `width` are x; bits past `width` in the top word stay 0 so they cannot
  // leak phantom x into reads or arithmetic of the value (a field write that
  // covers only part of a word would otherwise leave that garbage behind).
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].aval = ~uint64_t{0};
    var->value.words[i].bval = ~uint64_t{0};
  }
  if (uint32_t top_bits = width % 64; top_bits != 0 && var->value.nwords > 0) {
    uint64_t mask = (uint64_t{1} << top_bits) - 1;
    var->value.words[var->value.nwords - 1].aval &= mask;
    var->value.words[var->value.nwords - 1].bval &= mask;
  }
  variables_[name] = var;
  return var;
}

void SimContext::AliasVariable(std::string_view alias_name,
                               std::string_view target_name) {
  auto* target = FindVariable(target_name);
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
  // §6.18: nullifying one event handle must not disturb other handles that
  // alias the same underlying event. If this name shares its Variable with
  // another handle, rebind it to a fresh nulled event so the aliases diverge.
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
    // Canonical Convention A: x = (aval=1, bval=1) per bit.
    for (uint32_t i = 0; i < var->value.nwords; ++i) {
      var->value.words[i].aval = ~uint64_t{0};
      var->value.words[i].bval = ~uint64_t{0};
    }
  } else {
    // z (high impedance) until driven; Convention A z = (aval=0, bval=1).
    for (uint32_t i = 0; i < var->value.nwords; ++i) {
      var->value.words[i].aval = uint64_t{0};
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
  // §6.6.5: a tri0/tri1 net is equivalent to a wire carrying a continuous 0/1
  // of pull strength, so it holds that value even with no driver connected --
  // unlike an ordinary net, which stays z until driven. Resolve() with no
  // drivers installs the pull default (value and strength); a later driver
  // update re-resolves and can override it.
  // §28.15.3: a supply0/supply1 net models a constant ground/power connection.
  // Like tri0/tri1 above it holds its value (0/1) at supply strength with no
  // driver connected, so resolve it at creation instead of leaving it z.
  if (type == NetType::kTri0 || type == NetType::kTri1 ||
      type == NetType::kSupply0 || type == NetType::kSupply1) {
    net->Resolve(arena_);
  }
  return net;
}

void SimContext::SetCurrentProcess(Process* proc) {
  if (proc == current_process_) return;
  // §13.3.2: SetCurrentProcess is the thread-switch primitive -- every process
  // resume is preceded by a call here. Hand the scope stack off between threads
  // so automatic-task (and block) locals stay private to each activation: park
  // the outgoing process's stack and bring in the incoming process's. Static
  // storage is unaffected -- it lives in static_frames_, shared across
  // activations of the same instance.
  if (current_process_) {
    current_process_->saved_scope_stack = std::move(scope_stack_);
  }
  if (proc) {
    scope_stack_ = std::move(proc->saved_scope_stack);
  } else {
    scope_stack_.clear();
  }
  current_process_ = proc;
}

void SimContext::PushScope() { scope_stack_.emplace_back(); }

void SimContext::PopScope() {
  if (!scope_stack_.empty()) scope_stack_.pop_back();
}

std::vector<Scope> SimContext::SwapScopeStack(std::vector<Scope> new_stack) {
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
  scope_stack_.push_back(Scope{static_frames_[StaticFrameKey(func_name)], {}});
}

void SimContext::PopStaticScope(std::string_view func_name) {
  if (!scope_stack_.empty()) {
    static_frames_[StaticFrameKey(func_name)] = scope_stack_.back().vars;
    scope_stack_.pop_back();
  }
}

Variable* SimContext::FindLocalVariable(std::string_view name) {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); ++it) {
    auto found = it->vars.find(name);
    if (found != it->vars.end()) return found->second;
  }
  return nullptr;
}

Variable* SimContext::CreateLocalVariable(std::string_view name, uint32_t width,
                                          bool is_signed) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4VecVal(arena_, width, 0);
  // The declaration's signedness belongs both to the object and to the value
  // standing in it: reads go through the variable's flag, while a value taken
  // straight out of the cell carries its own.
  var->is_signed = is_signed;
  var->value.is_signed = is_signed;
  if (!scope_stack_.empty()) {
    scope_stack_.back().vars[name] = var;
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
    scope_stack_.back().vars[name] = var;
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
    SetCurrentProcess(proc);
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

std::string SimContext::ResolveInstanceScope(std::string_view ident) const {
  std::string prefix = ActiveInstancePrefix();
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

// §18.17: "The randsequence statement creates an automatic scope", so the
// array §18.17.7 declares within one of its rules is described by the scope
// and not by the design. The shape is copied into the arena because the frame
// holds a pointer, and the arena outlives every scope: what ends with the
// scope is the name standing for the array, which is the whole of the
// declaration.
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

// §23.9: "If it is declared locally, then the local item shall be used; if not,
// the search shall continue upward". An array a scope declares is therefore
// what its name reads while that scope is on the stack, and a like-named array
// RegisterArray recorded for the whole run is what the name reads again once
// the scope is gone.
const ArrayInfo* SimContext::FindArrayInfo(std::string_view name) const {
  for (auto frame = scope_stack_.rbegin(); frame != scope_stack_.rend();
       ++frame) {
    auto local = frame->arrays.find(name);
    if (local != frame->arrays.end()) return local->second;
  }
  auto it = array_infos_.find(name);
  return (it != array_infos_.end()) ? &it->second : nullptr;
}

}  // namespace delta
