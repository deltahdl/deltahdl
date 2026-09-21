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
#include "simulator/dpi_runtime.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"

namespace delta {

// Defined here, where CoverageDB is a complete type, so the owning unique_ptr
// member can be destroyed.
SimContext::~SimContext() {
  // §35.5.3: the C layer reaches this run's registry through a free function
  // (DpiForeignRuntime), so a run that installed one takes it back out when it
  // goes away rather than leaving a pointer to storage that no longer exists.
  // Another run's installation is left alone: the last run to install is the
  // one the foreign layer is talking to.
  if (dpi_runtime_ != nullptr && DpiForeignRuntime() == dpi_runtime_) {
    DpiSetForeignRuntime(nullptr);
  }
}

CoverageDB& SimContext::CoverageData() {
  // §19.9: an externally injected database wins; otherwise create the run's own
  // and reuse it on every later call so the coverage system tasks/functions all
  // see the same live data.
  if (coverage_db_ != nullptr) return *coverage_db_;
  if (!owned_coverage_db_) owned_coverage_db_ = std::make_unique<CoverageDB>();
  return *owned_coverage_db_;
}

ClockingManager& SimContext::AcquireClockingManager() {
  // A manager installed from outside is the run's, the way an installed DPI
  // registry is: §14's blocks, their events and their sampled values all have
  // to be the one set, and making a second here would leave the design's blocks
  // in one manager and the run's lookups in the other.
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
  // A registry installed from outside is the run's: §35 holds of whichever one
  // the calls go through, and making a second here would leave a design's
  // imports in one registry and its calls in the other.
  if (dpi_runtime_ != nullptr) {
    DpiSetForeignRuntime(dpi_runtime_);
    return *dpi_runtime_;
  }
  if (owned_dpi_runtime_ == nullptr) {
    owned_dpi_runtime_ = std::make_unique<DpiRuntime>();
  }
  dpi_runtime_ = owned_dpi_runtime_.get();
  // §35.5.3: the C layer has no handle to pass, so the registry a foreign
  // routine's svGetScope and svSetScope reach is installed here, where the
  // run's own registry is settled.
  DpiSetForeignRuntime(dpi_runtime_);
  return *owned_dpi_runtime_;
}

namespace {

// The symbol tables consulted during a hierarchical name lookup: the map from
// instance path to its module type, the flat variable table, and the names of
// the design's top-level modules (§23.6).
struct SymbolTables {
  const std::unordered_map<std::string, std::string>& instance_types;
  const std::unordered_map<std::string_view, Variable*>& variables;
  const std::unordered_set<std::string>& top_modules;
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
  if (Variable* under_top = LookupRestUnderMatchingInstance(
          "", lookup.head, lookup.rest, tables)) {
    return under_top;
  }
  // §23.6: the complete path to any object starts at a top-level module and
  // may be used from a parallel hierarchy, so "m.a" written in the other
  // top-level module n names m's `a`. Every top's declarations are keyed under
  // the empty prefix, while the instance type under it records one top alone,
  // so the others are answered by their names: the head names a top, and the
  // rest is the key. §23.6 also lets the first node be the top of the
  // hierarchy the path is used from, and an instance of the current scope
  // called `m` is answered by the walk above or by the plain lookup ahead of
  // it, so that instance stands ahead of a top of the same name.
  if (tables.top_modules.count(std::string(lookup.head)) == 0) return nullptr;
  auto top_it = tables.variables.find(lookup.rest);
  return (top_it != tables.variables.end()) ? top_it->second : nullptr;
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
// interface, program, or checker boundary is encountered", the order
// GenerateBlockKeys (sim_context_name_tables.cpp) spells the keys in.
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

bool SimContext::AssertCheckingEnabled(uint32_t type_bit,
                                       uint32_t directive_bit) const {
  if (!assert_checking_off_) return true;
  return (assert_checking_off_atype_ & type_bit) == 0 ||
         (assert_checking_off_dtype_ & directive_bit) == 0;
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
  // §32.4.3's rebuild stands in the instance that declared what is being
  // rebuilt, which is neither of the two below.
  if (prefix_override_.active) return prefix_override_.prefix;
  return current_process_ ? current_process_->inst_prefix
                          : lowering_inst_prefix_;
}

// §26.3 with §13.4: a bare name read inside a package subroutine's body is
// the package's own variable or one an import of the package brings in, held
// under the "package.name" keys PackageFrameKeys lists
// (sim_context_fileio.cpp); null outside any package frame or where no key
// holds the name.
Variable* SimContext::FindInPackageScope(std::string_view name) {
  for (const std::string& key : PackageFrameKeys(name)) {
    auto found = variables_.find(key);
    if (found != variables_.end()) return found->second;
  }
  return nullptr;
}

// §26.3 with §13.4, for a subroutine as FindInPackageScope for a variable: a
// bare callee inside a package's frame is the package's own subroutine,
// registered under "pkg::name" by RegisterPackageScopedSubroutines, or one an
// import of the package brings in; null outside any package frame or where
// no package holds the name.
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
  if (auto* in_package = FindInPackageScope(name)) return in_package;
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
  // than declared in an enclosing module at all, as is each element of an
  // imported array (IsImportedName). §23.4 adds a fourth: a module
  // declared inside the one instantiating it, of which that subclause says
  // "The outer name space is visible to the inner module so that any name
  // declared there can be used", so the boundary §23.9 draws is not there.
  // §23.6's `$root` is a fifth, answered above rather than here: it names the
  // top of the design outright rather than climbing to it, so no boundary
  // stands between the reference and what it reaches.
  if (prefix.empty() || dot != std::string_view::npos || IsImportedName(name) ||
      nested_decl_scopes_.count(std::string(prefix)) != 0) {
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

  // §6.8, Table 6-7: an uninitialized 4-state integral variable defaults to 'x,
  // which FillWithX writes inside the width and nowhere above it.
  FillWithX(var->value);
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
  // §37.44: a process reaching here is one the run has a thread for. This is
  // the one place every process passes through, which is what makes the list
  // the scheduler builds the run's threads rather than some of them.
  scheduler_.NoteThreadSwitch(proc);
  // §13.3.2: SetCurrentProcess is the thread-switch primitive -- every process
  // resume is preceded by a call here. Hand the scope stack off between threads
  // so automatic-task (and block) locals stay private to each activation: park
  // the outgoing process's stack and bring in the incoming process's. Static
  // storage is unaffected -- it lives in static_frames_, shared across
  // activations of the same instance.
  // §21.2.1.5: the named scopes travel with the process as its locals do.
  // §8.11 and §8.15: the object and the class a suspended class task's body
  // runs against travel with it too (Process::saved_this_stack).
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
}

// §9.3.2 with §8.6 and §13.3.2: a branch spawned inside a method runs on the
// object and in the class the method runs on, and its statements are
// statements of the enclosing scope, so they read and write its automatic
// locals -- the loop variable a `for (int j ...)` declared, the `automatic int
// k = j` the fork itself declared before spawning, a class task's local. The
// stacks are the spawning process's, live here while it runs, and the branch
// takes a copy of each as the state SetCurrentProcess installs when it first
// resumes; a scope maps names to the variables themselves, so the copy holds
// the same variables and a write on either side is seen on the other. Without
// this the branch started with no object and no scope: every property and
// local read 0 and a write reached nothing or a variable of the branch's own.
void SimContext::CopyCarriedStacksTo(Process& child) const {
  child.saved_this_stack = this_stack_;
  child.saved_method_class_stack = method_class_stack_;
  child.saved_scope_stack = scope_stack_;
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
  // §18.14.1: with no thread running the draw is being made while the design
  // is built, and it seeds a static process or a static-initializer object of
  // the instance being built, from that instance's own initialization RNG.
  return InitializationRng(lowering_inst_prefix_, default_seed_);
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
//
// The upward search from inside an instance reaches its own module first, and
// CreateChildModuleVariables (lowerer_child.cpp) records an array that module
// declares under the instance's prefix, so the prefixed name is what a bare
// reference from within the instance denotes and is tried ahead of the bare
// key, as FindQueue and FindVariable do; ScopedObjectKeys
// (sim_context_fileio.cpp) orders the keys, a package frame's own ahead of
// both. Asked by the bare key alone, an array declared in an instantiated
// module was no array to any reader: an element select read a bit of the
// carrier variable the lowerer creates under the name, foreach ran once per
// bit of that carrier, and $size, %p and an aggregate copy saw no array at
// all. The bare key stays the answer for an array of the enclosing scope, so
// a name that resolved before still does.
const ArrayInfo* SimContext::FindArrayInfo(std::string_view name) const {
  for (auto frame = scope_stack_.crbegin(); frame != VisibleFramesEnd();
       ++frame) {
    auto local = frame->arrays.find(name);
    if (local != frame->arrays.end()) return local->second;
  }
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = array_infos_.find(key);
    if (it != array_infos_.end()) return &it->second;
  }
  return nullptr;
}

}  // namespace delta
