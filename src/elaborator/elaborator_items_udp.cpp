#include <cmath>
#include <cstddef>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §33.6.1: the libraries are searched in the order they were declared, and a
// name reaches the cell held by the first library searched that holds one. A
// primitive is such a cell, so the primitive a name reaches is the one in the
// earliest searched library holding a primitive of that name -- and it is
// reached at all only when no design element of another kind sits in a library
// searched before it. A name whose primitive is out-ranked that way is naming
// the other element, not a primitive instance, so this answers nullptr for it.
//
// Where no search order is in force every library sits at the same position, so
// the first primitive of the name answers and it outranks nothing, which is
// what a compilation given no library map sees.
//
// §33.6.2: a configuration may select the libraries to search instead, and a
// library its list leaves out is not searched at all. A primitive is a cell a
// library holds, so a primitive held only by a library left out of the list is
// skipped here rather than ranked behind the listed ones -- the name reaches no
// primitive, exactly as it reaches no module under the same list.
//
// §33.6.3: a cell selection clause paired with a use expansion instead binds
// every cell of the selected name outright to the one library.cell the clause
// names, so where such a clause applies there is no search to rank libraries in
// and no list to exclude one. The name reaches the primitive the clause names
// even when the selected library list leaves that library out, and reaches no
// primitive at all when the clause names a cell of some other kind -- or names
// nothing that exists -- since a clause that has bound the name has settled it.
//
// §33.6.4: an instance selection clause naming a library list puts that list in
// force over the instance it names, and the list is inherited by every
// descendant of that instance. A primitive instantiated anywhere in that
// subhierarchy is therefore searched for in the inherited list rather than in
// the one the configuration's default clause named -- reaching a primitive the
// default clause's list would have excluded, and reaching none where the
// inherited list holds none, whatever the default clause's list holds.
namespace {

// The primitive named `name` whose library stands earliest in `order`, or
// nullptr where the list excludes every one of them. `nearest_pos` takes the
// position of the one answered, which is what a cell of another kind is ranked
// against afterwards.
UdpDecl* NearestUdpInSearchOrder(const CompilationUnit* unit,
                                 std::string_view name,
                                 const std::vector<std::string>& order,
                                 bool strict, size_t* nearest_pos) {
  UdpDecl* nearest = nullptr;
  for (auto* u : unit->udps) {
    if (u->name != name) continue;
    if (LibraryExcludedBySelectedList(u->library, order, strict)) continue;
    size_t pos = LibrarySearchPosition(u->library, order);
    if (nearest == nullptr || pos < *nearest_pos) {
      nearest = u;
      *nearest_pos = pos;
    }
  }
  return nearest;
}

}  // namespace

// §33.4.1.4/§33.4.1.6: the primitive a cell clause's use expansion binds every
// cell of `name` to. Nullopt where no clause selects the name, so the search
// below runs; a present value (possibly nullptr) is the binding, where nullptr
// means the named target does not exist.
std::optional<UdpDecl*> Elaborator::ResolveUdpUseOverride(
    std::string_view name) const {
  auto clause = cell_clause_use_overrides_.find(std::string(name));
  if (clause == cell_clause_use_overrides_.end()) return std::nullopt;
  if (!CellUseOverrideApplies(clause->second.src_lib, name, unit_)) {
    return std::nullopt;
  }
  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  const auto& ov = clause->second;
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindUdpInLibrary(target_lib, ov.use_cell, unit_);
}

UdpDecl* Elaborator::FindUdpByName(std::string_view name) const {
  if (auto bound = ResolveUdpUseOverride(name); bound.has_value()) {
    return *bound;
  }

  // The list the instance selection clause covering this instance passes down,
  // where there is one, in place of the one the default clause put in force. A
  // clause names its list outright, so the list it hands down is a list in
  // force wherever it reaches.
  const std::vector<std::string>* inherited =
      InstanceLiblistForPath(current_inst_path_, instance_liblist_overrides_);
  const std::vector<std::string>& order =
      inherited == nullptr ? library_order_ : *inherited;
  bool strict = inherited != nullptr || library_order_strict_;

  size_t nearest_pos = 0;
  UdpDecl* nearest =
      NearestUdpInSearchOrder(unit_, name, order, strict, &nearest_pos);
  if (nearest == nullptr) return nullptr;

  const ModuleDecl* other_kind = FindModule(name);
  if (other_kind == nullptr) return nearest;
  size_t other_pos = LibrarySearchPosition(other_kind->library, order);
  if (other_pos < nearest_pos) return nullptr;
  return nearest;
}

void Elaborator::ReclassifyForwardUdpInstances(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;

    // §33.6.4: a library list a configuration named for one instance governs
    // that instance, and this walk runs while the cell holding the
    // instantiation is being elaborated -- one level above the path such a
    // clause would carry. The search is therefore made under the
    // instantiation's own path, and the path is put back afterwards, so a
    // clause naming this very instance is the one the primitive is looked for
    // under. An instantiation with no instance name adds no level to reach.
    std::string saved_inst_path = current_inst_path_;
    if (!item->inst_name.empty()) {
      if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
      current_inst_path_.append(item->inst_name.data(), item->inst_name.size());
    }
    UdpDecl* udp = FindUdpByName(item->inst_module);
    current_inst_path_ = std::move(saved_inst_path);
    if (udp == nullptr) continue;

    item->kind = ModuleItemKind::kUdpInst;
    item->gate_inst_name = item->inst_name;
    item->inst_name = {};
    item->gate_terminals.clear();
    item->gate_terminals.reserve(item->inst_ports.size());
    for (const auto& [pname, pexpr] : item->inst_ports) {
      item->gate_terminals.push_back(pexpr);
    }
    item->inst_ports.clear();
    item->inst_ports_implicit.clear();
  }
}

// §29.8: records on `mod` every instance of a user-defined primitive that one
// instantiation writes, so that the primitive drives the nets its output
// terminals name. "Instances of UDPs are specified inside modules in the same
// manner as gates (see 28.3)", and a gate instance reaches simulation as the
// RtlirContAssign ElaborateGateInst (src/elaborator/elaborator_gates.cpp)
// appends; a primitive instance reaches it as the RtlirUdpInst
// Elaborator::ElaborateOneUdpInst appends. Append nothing and no instance's
// output terminal has a driver.
void Elaborator::ElaborateUdpInst(ModuleItem* item, RtlirModule* mod) {
  // §29.8: "An optional range may be specified for an array of UDP instances",
  // and "The terminal connection rules remain the same as outlined in 28.3.6",
  // so such a range is expanded here into one instance per array element the
  // way ElaborateGateInst (src/elaborator/elaborator_gates.cpp) expands the
  // range on an array of gates. ExpandInstanceArray
  // (src/elaborator/elaborator_helpers.h) is that one expansion, and it answers
  // false where every terminal is single-bit, leaving the range to record the
  // one instance it describes.
  if (item->inst_range_left != nullptr && item->inst_range_right != nullptr &&
      ExpandInstanceArray(item, mod, arena_, [this, mod](ModuleItem* element) {
        ElaborateOneUdpInst(element, mod);
      }))
    return;

  ElaborateOneUdpInst(item, mod);
}

// §29.8: appends the one RtlirUdpInst that the terminal list currently held on
// `item` describes -- a single instance, or one element of an expanded instance
// array.
//
// Resolve the declaration here rather than record the name for a later pass.
// Elaborator::FindUdpByName answers the library search order §33.6 defines
// under the configuration in force at this point of the walk, and that
// configuration is not readable from the RtlirModule afterwards. Where it
// answers nullptr the name reaches no primitive, so nothing is appended and
// nothing is reported: the unresolved name is already reported elsewhere, and a
// second report would name the same source position twice.
//
// §29.8's `udp_instance` production puts the output terminal first --
// `[ name_of_instance ] ( output_terminal , input_terminal { , input_terminal }
// )` -- so ModuleItem::gate_terminals splits at index 1. ModuleItem::gate_kind
// is not consulted, because Parser::ParseOneUdpInstance
// (src/parser/parser_udp.cpp:6) never writes it for a primitive instance.
//
// §29.8 admits two delays and no more: "Only two delays may be specified
// because z is not supported for UDPs". ModuleItem::gate_delay and
// ModuleItem::gate_delay_fall are therefore carried and
// ModuleItem::gate_delay_decay is not.
//
// RtlirUdpInst::gen_block_consts and RtlirUdpInst::gen_block_prefix are left at
// their defaults, which is what the gate path leaves on the RtlirContAssign it
// appends. Elaborator::ElaborateGenerateBlockItem
// (src/elaborator/elaborator_generate.cpp:122) stamps §27.4's loop-index values
// onto RtlirModule::processes and RtlirModule::assigns after the item is
// elaborated, and it does not stamp RtlirModule::udp_insts.
void Elaborator::ElaborateOneUdpInst(const ModuleItem* item, RtlirModule* mod) {
  const UdpDecl* decl = FindUdpByName(item->inst_module);
  if (decl == nullptr) return;
  if (item->gate_terminals.empty()) return;

  RtlirUdpInst inst;
  inst.decl = decl;
  inst.name = item->gate_inst_name;
  inst.loc = item->loc;
  inst.output = item->gate_terminals.front();
  inst.inputs.assign(item->gate_terminals.begin() + 1,
                     item->gate_terminals.end());
  inst.delay = item->gate_delay;
  inst.delay_fall = item->gate_delay_fall;
  inst.drive_strength0 = item->drive_strength0;
  inst.drive_strength1 = item->drive_strength1;
  mod->udp_insts.push_back(inst);
}

namespace {

// §25.9: returns the constant parameter-override values of a module instance
// when every override evaluates to a constant, or nullopt if the instance has
// no overrides or any override is non-constant.
std::optional<std::vector<int64_t>> TryConstEvalInstParams(
    const ModuleItem* item, const ScopeMap& scope) {
  if (item->inst_params.empty()) return std::nullopt;
  std::vector<int64_t> values;
  for (const auto& param : item->inst_params) {
    const Expr* pexpr = param.second;
    if (pexpr == nullptr) return std::nullopt;
    // §25.9 / §11.2.1: an instance parameter override may be any constant
    // expression, including a parameter of the enclosing module, so evaluate it
    // in that module's parameter scope so the recorded value can be matched
    // against a virtual interface's own override.
    auto v = ConstEvalInt(pexpr, scope);
    if (!v) return std::nullopt;
    values.push_back(*v);
  }
  return values;
}

// §17.2/§17.7/§25.9: the kind of the enclosing scope that governs which nested
// items and instances are legal. `kind_word` is the diagnostic noun ("program"
// or "checker") used when either flag is set.
struct ParentScopeKind {
  bool is_program;
  bool is_checker;
  std::string_view kind_word;
};

// §25.9: the per-module lookup tables that record each instance's resolved kind
// (interface/checker/program) so later passes can validate references against
// the instantiated kind. Holds references to the elaborator member tables.
struct InstClassTables {
  std::unordered_map<std::string_view, std::string_view>& interface_inst_types;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      interface_inst_param_values;
  std::unordered_set<std::string_view>& checker_inst_names;
  std::unordered_set<std::string_view>& program_inst_names;
};

// §25.9: records a module-instance whose resolved child is an interface,
// checker, or program into the corresponding lookup table so later passes can
// validate references against the instantiated kind.
void ClassifyInstantiatedChild(const ModuleItem* item, const ModuleDecl* child,
                               InstClassTables& tables, const ScopeMap& scope) {
  if (child->decl_kind == ModuleDeclKind::kInterface) {
    tables.interface_inst_types[item->inst_name] = item->inst_module;
    if (auto values = TryConstEvalInstParams(item, scope)) {
      tables.interface_inst_param_values[item->inst_name] = std::move(*values);
    }
  }
  if (child->decl_kind == ModuleDeclKind::kChecker) {
    tables.checker_inst_names.insert(item->inst_name);
  }
  if (child->decl_kind == ModuleDeclKind::kProgram) {
    tables.program_inst_names.insert(item->inst_name);
  }
}

// Emits the parent-scope legality diagnostics for a module-instance item whose
// resolved child is `child`: an interface may not instantiate a module, and a
// program or checker may only instantiate checkers.
void CheckModuleInstParentRules(const ModuleItem* item, const ModuleDecl* decl,
                                const ModuleDecl* child,
                                const ParentScopeKind& parent,
                                DiagEngine& diag) {
  if (decl->decl_kind == ModuleDeclKind::kInterface &&
      child->decl_kind == ModuleDeclKind::kModule) {
    diag.Error(item->loc,
               std::format("module '{}' cannot be instantiated inside "
                           "interface '{}'",
                           item->inst_module, decl->name),
               Subclause("25.3"));
  }
  if ((parent.is_program || parent.is_checker) &&
      child->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("only checkers can be instantiated inside "
                           "{} '{}'",
                           parent.kind_word, decl->name),
               Subclause("17.2"));
  }
}

// §17.5: walks a procedural statement tree looking for a blocking assignment.
// Recurses only through control-flow bodies (block, branch arms, loop body,
// case arms, fork arms, and a wrapping timing control's body); the for-loop
// header (init/step) is intentionally not traversed, so a loop's own iteration
// update is not mistaken for a blocking assignment in the procedure body.
bool StmtContainsBlockingAssignment(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  if (stmt->kind == StmtKind::kBlockingAssign) return true;
  for (const auto* s : stmt->stmts)
    if (StmtContainsBlockingAssignment(s)) return true;
  for (const auto* s : stmt->fork_stmts)
    if (StmtContainsBlockingAssignment(s)) return true;
  for (const auto& ci : stmt->case_items)
    if (StmtContainsBlockingAssignment(ci.body)) return true;
  return StmtContainsBlockingAssignment(stmt->then_branch) ||
         StmtContainsBlockingAssignment(stmt->else_branch) ||
         StmtContainsBlockingAssignment(stmt->for_body) ||
         StmtContainsBlockingAssignment(stmt->body);
}

// §17.5: walks a procedural statement tree looking for a timing control that is
// not an event control. Statement-level delay, cycle-delay, wait, and wait-fork
// controls are rejected, as is an intra-assignment delay or cycle delay on an
// assignment. An event control statement is itself permitted, but its
// controlled statement is still inspected in case a non-event control is nested
// inside.
bool StmtContainsNonEventTimingControl(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  switch (stmt->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      // An intra-assignment event (`x <= @(ev) y;`) is an event control and is
      // allowed; only an intra-assignment delay or cycle delay is rejected.
      if (stmt->delay != nullptr || stmt->cycle_delay != nullptr) return true;
      break;
    default:
      break;
  }
  for (const auto* s : stmt->stmts)
    if (StmtContainsNonEventTimingControl(s)) return true;
  for (const auto* s : stmt->fork_stmts)
    if (StmtContainsNonEventTimingControl(s)) return true;
  for (const auto& ci : stmt->case_items)
    if (StmtContainsNonEventTimingControl(ci.body)) return true;
  return StmtContainsNonEventTimingControl(stmt->then_branch) ||
         StmtContainsNonEventTimingControl(stmt->else_branch) ||
         StmtContainsNonEventTimingControl(stmt->for_body) ||
         StmtContainsNonEventTimingControl(stmt->body);
}

// Emits the per-item legality diagnostics that depend only on the parent decl
// kind (no instance resolution): forbidden primitives/nets/always/nested decls
// inside programs/checkers/interfaces, and records port-less nested programs.
// §17.5/§17.7: the rules that govern what a checker body may contain -- no
// nets, no general `always`, no blocking assignment in an always_ff, only
// event-controlled timing in an initial procedure, and no design element other
// than a further checker.
void CheckCheckerBodyItemRules(const ModuleItem* item, const ModuleDecl* decl,
                               const ParentScopeKind& parent,
                               DiagEngine& diag) {
  if (!parent.is_checker) return;
  // §17.7: a checker body may define variables but not nets.
  if (item->kind == ModuleItemKind::kNetDecl) {
    diag.Error(item->loc,
               std::format("a net cannot be declared inside checker '{}'; "
                           "only variables may be defined in a checker body",
                           decl->name),
               Subclause("17.7"));
  }
  // §17.5: the only always procedures a checker admits are always_comb,
  // always_latch, and always_ff; a general 'always' is not among them (also
  // reflected in Annex C.2.7's removal of general always for checkers).
  if (item->kind == ModuleItemKind::kAlwaysBlock) {
    diag.Error(item->loc,
               std::format("a general 'always' procedure cannot be used "
                           "inside checker '{}'; use always_comb, "
                           "always_latch, or always_ff instead",
                           decl->name),
               Subclause("17.5"));
  }
  // §17.5/§17.7.1: a checker always_ff procedure may not use blocking
  // assignments (§17.7.1 states that only nonblocking assignments are allowed
  // there); blocking assignments are permitted only in always_comb and
  // always_latch.
  if (item->kind == ModuleItemKind::kAlwaysFFBlock &&
      StmtContainsBlockingAssignment(item->body)) {
    diag.Error(item->loc,
               std::format("a blocking assignment cannot appear in an "
                           "always_ff procedure of checker '{}'; use a "
                           "nonblocking assignment, or move it to an "
                           "always_comb or always_latch procedure",
                           decl->name),
               Subclause("17.7.1"));
  }
  // §17.5: an initial procedure in a checker body "may contain let
  // declarations, immediate, deferred, and concurrent assertions, and a
  // procedural timing control statement using an event control only". A.6.5
  // gives procedural_timing_control three alternatives -- delay_control,
  // event_control and cycle_delay -- so the other two are both excluded, as is
  // a wait. The message names all three rather than only the delay forms,
  // because a cycle delay is the one most easily mistaken for an event control:
  // §14.11 defines it as a wait for clocking block events, but the grammar
  // makes it its own alternative rather than an event_control.
  if (item->kind == ModuleItemKind::kInitialBlock &&
      StmtContainsNonEventTimingControl(item->body)) {
    diag.Error(item->loc,
               std::format("an initial procedure in checker '{}' may use only "
                           "an event control for timing; a delay, a cycle "
                           "delay and a wait are not allowed",
                           decl->name),
               Subclause("17.5"));
  }
  // §17.2: only further checkers may be declared inside a checker.
  if (item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("a module, interface, or program cannot be "
                           "declared inside checker '{}'",
                           decl->name),
               Subclause("17.2"));
  }
}

// §23.4/§25.9: the rules that govern a design element declared inside another.
// A port-less nested program is implicitly instantiated, so its name is
// recorded; a module may not be declared inside an interface.
void CheckNestedDeclItemRules(
    const ModuleItem* item, const ModuleDecl* decl,
    std::unordered_set<std::string_view>& program_inst_names,
    DiagEngine& diag) {
  if (item->kind != ModuleItemKind::kNestedModuleDecl ||
      !item->nested_module_decl)
    return;
  if (item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram &&
      item->nested_module_decl->ports.empty()) {
    program_inst_names.insert(item->nested_module_decl->name);
  }
  if (decl->decl_kind == ModuleDeclKind::kInterface &&
      item->nested_module_decl->decl_kind == ModuleDeclKind::kModule) {
    diag.Error(item->loc,
               std::format("module '{}' cannot be declared inside "
                           "interface '{}'",
                           item->nested_module_decl->name, decl->name),
               Subclause("25.3"));
  }
}

void CheckProgramCheckerItemRules(
    const ModuleItem* item, const ModuleDecl* decl,
    const ParentScopeKind& parent,
    std::unordered_set<std::string_view>& program_inst_names,
    DiagEngine& diag) {
  if ((parent.is_program || parent.is_checker) &&
      item->kind == ModuleItemKind::kUdpInst) {
    diag.Error(item->loc,
               std::format("primitive cannot be instantiated inside "
                           "{} '{}'",
                           parent.kind_word, decl->name),
               Subclause("24.3"));
  }
  CheckCheckerBodyItemRules(item, decl, parent, diag);
  CheckNestedDeclItemRules(item, decl, program_inst_names, diag);
}

// Returns true if a child instance named `name` already exists on the module,
// i.e. the nested module was explicitly instantiated by the source.
bool ModuleExplicitlyInstantiated(const RtlirModule* mod,
                                  std::string_view name) {
  for (const auto& child : mod->children) {
    if (child.module_name == name) return true;
  }
  return false;
}

// Indexes the nested module/interface/program declarations of `decl` by name
// and rejects a virtual-interface variable declared directly inside an
// interface body.
void CollectNestedModulesAndCheckVif(
    const ModuleDecl* decl,
    std::unordered_map<std::string_view, ModuleDecl*>& nested_module_decls,
    DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl && !item->nested_module_decl->is_extern) {
      // §23.5: an extern module declaration only declares the ports; it never
      // defines an instantiable module. Keep it out of the nested-module table
      // so it is not elaborated or instantiated as a real module and does not
      // shadow the actual nested definition of the same name.
      nested_module_decls[item->nested_module_decl->name] =
          item->nested_module_decl;
    }
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      diag.Error(item->loc,
                 "virtual interface cannot be declared inside an interface",
                 Subclause("25.9"));
    }
  }
}

// Records task names and indexes function declarations by name.
void RecordTaskFuncNames(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls[item->name] = item;
    }
  }
}

// §6.21/§13.3.1: a task/function with no explicit lifetime inherits the
// enclosing scope's lifetime (automatic if the scope is automatic, otherwise
// static).
void DefaultSubroutineLifetimes(const std::vector<ModuleItem*>& items,
                                bool scope_is_automatic) {
  for (auto* item : items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        !item->is_automatic && !item->is_static) {
      if (scope_is_automatic) {
        item->is_automatic = true;
      } else {
        item->is_static = true;
      }
    }
  }
}

void DefaultTaskFuncLifetimes(const ModuleDecl* decl) {
  DefaultSubroutineLifetimes(decl->items, decl->is_automatic);
}

// Collects the names of the automatic-lifetime tasks and functions.
void CollectAutoTaskFuncNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& auto_task_func_names) {
  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl) &&
        item->is_automatic) {
      auto_task_func_names.insert(item->name);
    }
  }
}

// Records task and function declaration names, defaults their lifetime from the
// enclosing decl (§6.21), and collects the automatic ones. Mutates the three
// member tables passed by reference.
void ClassifyTaskFuncDecls(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    std::unordered_set<std::string_view>& auto_task_func_names) {
  RecordTaskFuncNames(decl, task_names, func_decls);
  DefaultTaskFuncLifetimes(decl);
  CollectAutoTaskFuncNames(decl, auto_task_func_names);
}

// §23.2/§25.9: the enclosing design element an item is classified within --
// what kind of scope it is, the parameter scope an instance's overrides fold
// in, and where a violation is reported.
struct ItemScopeContext {
  const ParentScopeKind& parent_scope;
  const ScopeMap& scope;
  DiagEngine& diag;
};

// §17.2/§17.7/§25.9: applies instance-classification and parent-scope legality
// rules to every item of `decl`; `find_child` resolves an instance's target.
template <typename FindChild>
void ClassifyAndCheckItems(const ModuleDecl* decl,
                           const ItemScopeContext& item_scope,
                           InstClassTables& inst_class_tables,
                           FindChild&& find_child) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      const ModuleDecl* child = find_child(item->inst_module);
      if (child) {
        ClassifyInstantiatedChild(item, child, inst_class_tables,
                                  item_scope.scope);
        CheckModuleInstParentRules(item, decl, child, item_scope.parent_scope,
                                   item_scope.diag);
      }
    }
    CheckProgramCheckerItemRules(item, decl, item_scope.parent_scope,
                                 inst_class_tables.program_inst_names,
                                 item_scope.diag);
  }
}

// §16.12/§F.4.1: registers every property/sequence decl of `decl` into
// `registry` so a property may be referenced before its declaration.
void BuildPropertyRegistry(const ModuleDecl* decl, PropertyRegistry& registry) {
  registry = PropertyRegistry();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl ||
        item->kind == ModuleItemKind::kSequenceDecl) {
      registry.Register(item);
    }
  }
}

// True if port-less nested module `nested_decl` (named `name`) is an implicit-
// instantiation candidate: not an interface and not explicitly instantiated.
bool IsImplicitNestedInstantiationCandidate(std::string_view name,
                                            const ModuleDecl* nested_decl,
                                            const RtlirModule* mod) {
  if (!nested_decl->ports.empty()) return false;
  if (nested_decl->decl_kind == ModuleDeclKind::kInterface) return false;
  if (ModuleExplicitlyInstantiated(mod, name)) return false;
  return true;
}

}  // namespace

// §13.3.1: subroutines declared in a package take their default lifetime from
// the package. Packages are not elaborated through ElaborateItems (they are not
// modules), so their task/function default lifetimes are resolved here.
void Elaborator::DefaultPackageTaskFuncLifetimes() {
  for (auto* pkg : unit_->packages) {
    DefaultSubroutineLifetimes(pkg->items, pkg->is_automatic);
  }
}

void Elaborator::RunPostItemValidations(const ModuleDecl* decl,
                                        RtlirModule* mod) {
  CheckAlwaysCombMultiDriver(decl, mod);
  CheckAggregateElementDrivers(decl, mod);
  ValidateModuleConstraints(decl, mod);
  ValidateValueParams(decl, mod);
  ValidateLhsPatternWidths(decl, mod);
  ValidateClockvarAccess(decl);
  ValidateCycleDelayDefaultClocking(decl);
  ValidateIntraAssignCycleDelay(decl);
  ValidateDuplicateDefaultClocking(decl);
  ValidateDefaultClockingReference(decl);
  ValidateDuplicateGlobalClocking(decl);
  ValidateDuplicateDefaultDisableIff(decl);
  ValidateGlobalClockReference(decl);
  ValidateGclkRequiresGlobalClocking(decl);
  ValidateFutureGclkPlacement(decl);
  ValidateContAssignToClockvar(decl);
  ValidatePrimitiveDriveToClockvar(decl);
  ValidateSyncDriveForm(decl);
  ValidateConstantFunctionCalls(decl);
  ValidateDpiOpenArrayArgs(decl);
  ValidateBackgroundFuncCallContext(decl);
  ValidateParameterizedMailboxCalls(decl);
  ValidateSequenceEventArgs(decl);
  ValidateHierRefIntoChecker(decl);
  ValidateFreeCheckerVariableAssignments(decl);
  ValidateCheckerVariableInitialAssignment(decl);
  ValidateHierRefIntoProgram(decl);
  ValidateProgramSubroutineCall(decl);
  ValidateHierRefToAutomatic(decl);
  ValidateHierRefToImportedName(decl, mod);
  ValidateUnresolvedReferences(decl, mod);
  ValidateHierRefInstanceArray(decl, mod);
  ValidateForwardTypedefsInScope(decl);
  ValidateForwardTypedefScopePrefix(decl);
}

// §8.25.1: the parameterized-class declarations of a compilation unit, indexed
// by class name. Only a class with parameter ports can be specialized, so only
// those are exposed to the constant folder.
std::unordered_map<std::string_view, const ClassDecl*> BuildParamClassRegistry(
    const CompilationUnit* unit) {
  std::unordered_map<std::string_view, const ClassDecl*> registry;
  for (const auto* cls : unit->classes) {
    if (cls && !cls->params.empty()) registry.emplace(cls->name, cls);
  }
  return registry;
}

void Elaborator::InstantiateImplicitNestedModules(
    const std::vector<std::pair<std::string_view, ModuleDecl*>>& nested,
    RtlirModule* mod) {
  for (const auto& [name, nested_decl] : nested) {
    if (!IsImplicitNestedInstantiationCandidate(name, nested_decl, mod))
      continue;
    if (HasParamPortWithoutDefault(nested_decl)) continue;
    RtlirModuleInst inst;
    inst.module_name = name;
    inst.inst_name = name;
    inst.simple_inst_name = name;
    // §23.4: this instance exists because the module was declared here, so the
    // enclosing scope's names are visible inside it.
    inst.is_nested_decl = true;
    ParamList empty_params;

    std::string saved_inst_path = current_inst_path_;
    if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
    current_inst_path_.append(name.data(), name.size());
    // §23.9/§24.3: a nested module/program/interface resolves names declared in
    // this enclosing scope, so hand its visible names to ElaborateModule.
    pending_enclosing_scope_ = CaptureCurrentScopeNames();
    has_pending_enclosing_scope_ = true;
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    mod->children.push_back(inst);
  }
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  ReclassifyForwardUdpInstances(decl);
  // §23.2.2.1: do NOT reset the per-module item-elaboration state here.
  // ElaborateModule already reset it via the ItemElaborationStateSaver before
  // ElaboratePorts ran, and ElaboratePorts populated the ANSI/non-ANSI
  // port-name tables (complete/partial/signed ports) that the body net and
  // variable declarations below reconcile against. Re-running the reset would
  // wipe those tables before reconciliation, silently dropping the
  // redeclaration, range-mismatch, and signedness checks.
  CollectNestedModulesAndCheckVif(decl, nested_module_decls_, diag_);
  const bool kParentIsProgram = decl->decl_kind == ModuleDeclKind::kProgram;
  const bool kParentIsChecker = decl->decl_kind == ModuleDeclKind::kChecker;
  const ParentScopeKind kParentScope{kParentIsProgram, kParentIsChecker,
                                     kParentIsProgram
                                         ? std::string_view{"program"}
                                         : std::string_view{"checker"}};
  InstClassTables inst_class_tables{interface_inst_types_,
                                    interface_inst_param_values_,
                                    checker_inst_names_, program_inst_names_};

  ClassifyAndCheckItems(
      decl, {kParentScope, BuildParamScope(mod), diag_}, inst_class_tables,
      [&](std::string_view name) { return FindModuleInScope(name); });

  for (const auto& [pname, pval] : decl->params) {  // §6.20: params are consts.
    const_names_.insert(pname);
  }

  ClassifyTaskFuncDecls(decl, task_names_, func_decls_, auto_task_func_names_);

  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());

  BuildPropertyRegistry(decl, property_registry_);

  // §13.4.3: make this scope's functions available to the constant-expression
  // folder so a parameter/localparam initialized from a constant function call
  // (e.g. `localparam addr_width = clogb2(ram_depth)`) is evaluated at
  // elaboration time while its declaration item is elaborated below.
  ConstFuncRegistryGuard const_func_guard(&func_decls_);

  // §8.25.1: also expose the parameterized-class declarations so a constant
  // expression that reads a specific specialization's parameter through the
  // scope resolution operator (e.g. `localparam W = C#(3)::p`) folds to that
  // specialization's value rather than the class default.
  std::unordered_map<std::string_view, const ClassDecl*> param_class_registry =
      BuildParamClassRegistry(unit_);
  ParamClassRegistryGuard param_class_guard(&param_class_registry);

  // §11.5.1: expose this module's parameter declarations so a bit-select or
  // part-select written on one of them (e.g. `localparam Q = P[8:5]`) is
  // resolved against the range P was declared with. The module is consulted at
  // each fold rather than copied, so a parameter declared earlier in this item
  // list is visible to a select written later in it.
  ParamRangeRegistryGuard param_range_guard(mod);

  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }

  InstantiateImplicitNestedModules(local_nested_modules, mod);

  RunPostItemValidations(decl, mod);
}

}  // namespace delta
