#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/checker_procedure_rules.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/disable_iff_resolution.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_gen_block_interfaces.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/interface_property_instance.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

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
// resolved child is `child`: an interface may not instantiate a module, a
// program may instantiate no module, interface or program (§24.3), reported as
// the parser reports one whose cell it has seen declared, and a checker may
// instantiate only checkers (§17.2).
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
  if (child->decl_kind == ModuleDeclKind::kChecker) return;
  if (parent.is_program) {
    diag.Error(item->loc, "instantiations not allowed in programs",
               Subclause("24.3"));
    return;
  }
  if (parent.is_checker) {
    diag.Error(item->loc,
               std::format("only checkers can be instantiated inside "
                           "{} '{}'",
                           parent.kind_word, decl->name),
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

// §24.3: a program or checker instantiates no user-defined primitive.
void CheckUdpInstParentRule(const ModuleItem* item, const ModuleDecl* decl,
                            const ParentScopeKind& parent, DiagEngine& diag) {
  if (!parent.is_program && !parent.is_checker) return;
  diag.Error(item->loc,
             std::format("primitive cannot be instantiated inside "
                         "{} '{}'",
                         parent.kind_word, decl->name),
             Subclause("24.3"));
}

void CheckProgramCheckerItemRules(
    const ModuleItem* item, const ModuleDecl* decl,
    const ParentScopeKind& parent,
    std::unordered_set<std::string_view>& program_inst_names,
    DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kUdpInst) {
    CheckUdpInstParentRule(item, decl, parent, diag);
  }
  CheckCheckerBodyItemRules(item, decl, parent.is_checker, diag);
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
//
// §35.5: an imported function is used much as a native SystemVerilog function
// is, so a subroutine §35.5.4 declared with the `task` keyword is a task of
// this scope and is recorded as one. §13.4's rule that a function shall not
// enable a task reads this set, and §35.5.1.1's note that an imported task can
// consume time is why that rule has to reach one.
void RecordTaskFuncNames(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kDpiImport && item->dpi_is_task) {
      task_names.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls[item->name] = item;
    }
  }
}

// §13.4.3 with §26.3: a constant function declared in a package is called
// through the package scope resolution operator, `pk::twice(6)`, so every
// package's functions are registered under that key in the table the folder
// reads; an out-of-block class method (§8.24) is the class's and is left out.
// The key is arena-owned, as the table holds views. An import registers the
// bare name (RegisterImportItem in elaborator_import.cpp).
static void RecordPackageFuncNames(
    const CompilationUnit* unit,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    Arena& arena) {
  for (const auto* pkg : unit->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kFunctionDecl ||
          !item->method_class.empty()) {
        continue;
      }
      auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                            "::" + std::string(item->name));
      func_decls[*key] = item;
    }
  }
}

// §6.21/§13.3.1: a task/function with no explicit lifetime inherits the
// enclosing scope's lifetime (automatic if the scope is automatic, otherwise
// static). An out-of-block method body (§8.24), the item whose `method_class`
// names its class, is left alone: §8.6 makes every method of a class automatic
// and forbids a class method a static lifetime, so the scope's default is not
// its to inherit. The simulator reads ModuleItem::is_static_method for §8.10's
// qualifier; before the two flags were split, marking a body here made an
// instance method of a package class run in class scope without `this`, its
// properties unreachable.
void DefaultSubroutineLifetimes(const std::vector<ModuleItem*>& items,
                                bool scope_is_automatic) {
  for (auto* item : items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        item->method_class.empty() && !item->is_automatic && !item->is_static) {
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

// §3.4 (printed page 51) with §27: a generate block is part of the design
// element it is written in, so an instance in one -- in the body, the else
// body or a case arm of the generate construct `item`, at any depth -- is held
// to the placement rules of §25.3, §17.2 and §24.3 that the element's own
// items are. A user-defined primitive declared after the element is still
// read as a module instance there, so `is_udp` names one by its name.
template <typename FindChild, typename IsUdp>
void CheckGeneratePlacement(const ModuleItem* item, const ModuleDecl* decl,
                            const ItemScopeContext& item_scope,
                            FindChild& find_child, IsUdp& is_udp) {
  auto check = [&](const ModuleItem* sub) {
    if (sub->kind == ModuleItemKind::kModuleInst) {
      const ModuleDecl* child = find_child(sub->inst_module);
      if (child != nullptr) {
        CheckModuleInstParentRules(sub, decl, child, item_scope.parent_scope,
                                   item_scope.diag);
      } else if (is_udp(sub->inst_module)) {
        CheckUdpInstParentRule(sub, decl, item_scope.parent_scope,
                               item_scope.diag);
      }
    }
    if (sub->kind == ModuleItemKind::kUdpInst) {
      CheckUdpInstParentRule(sub, decl, item_scope.parent_scope,
                             item_scope.diag);
    }
    CheckGeneratePlacement(sub, decl, item_scope, find_child, is_udp);
  };
  for (const auto* sub : item->gen_body) check(sub);
  if (item->gen_else != nullptr) check(item->gen_else);
  for (const auto& arm : item->gen_case_items) {
    for (const auto* sub : arm.body) check(sub);
  }
}

// §17.2/§17.7/§25.9: applies instance-classification and parent-scope legality
// rules to every item of `decl`; `find_child` resolves an instance's target.
template <typename FindChild, typename IsUdp>
void ClassifyAndCheckItems(const ModuleDecl* decl,
                           const ItemScopeContext& item_scope,
                           InstClassTables& inst_class_tables,
                           FindChild&& find_child, IsUdp&& is_udp) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      const ModuleDecl* child = find_child(item->inst_module);
      if (child) {
        ClassifyInstantiatedChild(item, child, inst_class_tables,
                                  item_scope.scope);
        CheckModuleInstParentRules(item, decl, child, item_scope.parent_scope,
                                   item_scope.diag);
        CheckCheckerInstForm(item, child, item_scope.diag);
      }
    }
    CheckProgramCheckerItemRules(item, decl, item_scope.parent_scope,
                                 inst_class_tables.program_inst_names,
                                 item_scope.diag);
    CheckGeneratePlacement(item, decl, item_scope, find_child, is_udp);
  }
}

// §16.16 (b): every sequence and property declaration within a clocking
// block is treated as though the block's clocking event had been written
// as its leading clocking event, and an assertion instantiates it by the
// name of the block and its own, `posedge_clk.q4`, which is the name the
// registry keys it under, once, the declaration being shared by every
// instance of the module.
void RegisterClockingBlockDecls(const ModuleItem* block,
                                PropertyRegistry& registry, Arena& arena) {
  for (ModuleItem* decl : block->clocking_decls) {
    if (decl->name.find('.') == std::string_view::npos) {
      auto* qualified = arena.Create<std::string>(
          std::string(block->name) + "." + std::string(decl->name));
      decl->name = *qualified;
    }
    if (decl->kind == ModuleItemKind::kPropertyDecl &&
        decl->prop_clock.empty()) {
      decl->prop_clock = block->clocking_event;
    }
    if (decl->kind == ModuleItemKind::kSequenceDecl &&
        decl->seq_clock.empty()) {
      decl->seq_clock = block->clocking_event;
    }
    registry.Register(decl);
  }
}

// §16.12/§F.4.1: registers every property/sequence decl of `decl` into
// `registry` so a property may be referenced before its declaration.
void BuildPropertyRegistry(const ModuleDecl* decl, PropertyRegistry& registry,
                           Arena& arena) {
  registry = PropertyRegistry();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl ||
        item->kind == ModuleItemKind::kSequenceDecl) {
      registry.Register(item);
    }
    if (item->kind == ModuleItemKind::kClockingBlock) {
      RegisterClockingBlockDecls(item, registry, arena);
    }
  }
}

// §26.3: whether the scope whose items are `items` imports `name` from `pkg`,
// by a wildcard import of the package or by an import of the name.
bool ImportsName(const std::vector<ModuleItem*>& items, std::string_view pkg,
                 std::string_view name) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (imp.package_name != pkg) continue;
    if (imp.is_wildcard || imp.item_name == name) return true;
  }
  return false;
}

// §16.8 and §16.12 with §26.3: the named sequences and properties declared in
// a package are reached from the module through the package scope,
// "pk::name", and by their bare names where the module or the compilation
// unit imports them; the module's own declarations, registered first, keep
// their names.
void RegisterPackageAssertionDecls(const ModuleDecl* decl,
                                   const CompilationUnit* unit,
                                   PropertyRegistry& registry, Arena& arena) {
  if (unit == nullptr) return;
  for (const PackageDecl* pkg : unit->packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind != ModuleItemKind::kPropertyDecl &&
          item->kind != ModuleItemKind::kSequenceDecl) {
        continue;
      }
      registry.RegisterAs(
          *arena.Create<std::string>(std::string(pkg->name) +
                                     "::" + std::string(item->name)),
          item);
      if (ImportsName(decl->items, pkg->name, item->name) ||
          ImportsName(unit->cu_items, pkg->name, item->name)) {
        registry.RegisterAs(item->name, item);
      }
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
  ValidateClockingSignalTargets(decl);
  ValidateCycleDelayCounts(decl, BuildParamScope(mod), diag_);
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
  ValidateTaskCallsInExpressions(decl);
  ValidateBackgroundFuncCallContext(decl);
  ValidateParameterizedMailboxCalls(decl);
  ValidateStdClassMethodCalls(decl);
  ValidateSequenceEventArgs(decl, mod);
  ValidateHierRefIntoChecker(decl);
  ValidateFreeCheckerVariableAssignments(decl);
  ValidateCheckerVariableInitialAssignment(decl);
  ValidateCheckerProcedureCovergroups(decl, diag_);
  ValidateCheckerAssignmentCalls(decl, diag_);
  ValidateHierRefIntoProgram(decl);
  ValidateProgramSubroutineCall(decl);
  ValidateProgramWideSpaceAccess(decl);
  ValidateHierRefToAutomatic(decl);
  ValidateHierRefToImportedName(decl, mod);
  ValidateUnresolvedReferences(decl, mod);
  ValidateHierRefInstanceArray(decl, mod);
  ValidateForwardTypedefsInScope(decl->items);
  ValidateForwardTypedefScopePrefix(decl);
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
    std::string saved_config_path = std::exchange(
        config_inst_path_, HierInstancePath(config_inst_path_, {}, name));
    // §23.9/§24.3: a nested module/program/interface resolves names declared in
    // this enclosing scope, so hand its visible names to ElaborateModule. The
    // instance is implied at the end of the items, but §6.10 counts a name as
    // declared previously by the text above the nested declaration, so the
    // snapshot ElaborateItems took there is what BeginNestedDeclScope prefers.
    BeginNestedDeclScope(nested_decl, CaptureCurrentScopeNames());
    nested_default_disable_iff_ = mod->default_disable_iff;
    nested_default_clock_ = DefaultClockingEvent(mod);
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    config_inst_path_ = std::move(saved_config_path);
    mod->children.push_back(inst);
  }
}

// The items of `decl` in source order, each seeing only the names declared
// above it, then the delayed signals its timing checks imply.
void Elaborator::ElaborateItemsInOrder(const ModuleDecl* decl,
                                       RtlirModule* mod) {
  // §6.10 with §23.4: a reference inside a nested declaration sees an outer
  // name only if it was declared previously, above the declaration's text. An
  // instance written above its declaration is elaborated before the loop
  // below reaches the declaration, so the names the text declares above each
  // nested declaration are read first, for BeginNestedDeclScope to join with
  // the names declared so far at such an instance.
  RecordNestedDeclNamesAbove(decl->items);
  // §3.13 (e): an interface's modports are in its module name space too; they
  // are held apart from its items, so they enter it before the items do.
  for (const auto* modport : decl->modports) {
    DeclareInModuleNameSpace(modport->name, modport->loc);
  }
  for (auto* item : decl->items) {
    // The same rule for an instance written or implied below: this scope's
    // names are recorded as they stand when the loop reaches the declaration,
    // for BeginNestedDeclScope to hand on when the instance is elaborated.
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl != nullptr) {
      nested_decl_scope_names_[item->nested_module_decl] =
          CaptureCurrentScopeNames();
    }
    ElaborateItem(item, mod);
  }
  for (auto* item : TimingCheckDelayedSignalItems(decl, arena_)) {
    ElaborateItem(item, mod);
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
      [&](std::string_view name) { return FindModuleInScope(name); },
      [&](std::string_view name) { return FindUdpByName(name) != nullptr; });
  RegisterGenerateBlockInterfaces(
      decl->items,
      [&](std::string_view name) { return FindModuleInScope(name); },
      interface_inst_types_, arena_);

  for (const auto& [pname, pval] : decl->params) {  // §6.20: params are consts.
    const_names_.insert(pname);
  }

  ClassifyTaskFuncDecls(decl, task_names_, func_decls_, auto_task_func_names_);
  RecordPackageFuncNames(unit_, func_decls_, arena_);
  inference_funcs_ = InferenceFuncs{func_decls_, {}};

  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());

  BuildPropertyRegistry(decl, property_registry_, arena_);
  RegisterPackageAssertionDecls(decl, unit_, property_registry_, arena_);
  RegisterInterfaceInstanceProperties(
      decl, unit_, property_registry_, arena_,
      {mod->property_decls, mod->sequence_decls});
  PromoteSequenceInstancesInProperties(decl, property_registry_, arena_);
  // §16.15: the default disable iff of this scope, wherever it stands among
  // the items, or the enclosing declaration's where this is a nested
  // declaration without one, which the concurrent assertions of the scope
  // without a disable iff clause of their own take.
  mod->default_disable_iff = DeclaredDefaultDisableIff(decl->items);
  if (mod->default_disable_iff == nullptr) {
    mod->default_disable_iff = inherited_default_disable_iff_;
  }
  mod->inherited_default_clock = inherited_default_clock_;

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
  // §20.6.2 with §6.18: expose this scope's typedefs so `$bits(my_t)` written
  // in a parameter's value is sized by the type the name stands for, and the
  // names among them that stand for an unpacked aggregate, which have no
  // single width and are left to the run. The table is consulted at each fold
  // as the module is, so a typedef declared earlier in this item list is
  // visible to a call written later in it.
  TypedefRegistryGuard typedef_guard(&typedefs_, &aggregate_typedef_names_);
  // §23.9: this runs while the module is being elaborated, so a UDP instance
  // written in a generate block reads that block's parameters as well as the
  // module's, and gen_prefix_scopes_ is already where the instance stands.
  RegisteredGenScopeGuard gen_scope_guard(gen_prefix_scopes_);

  ElaborateItemsInOrder(decl, mod);

  // §6.18: a class method's or a module subroutine's formal may name a
  // typedef the module forward-declares above it and defines below it, so
  // every class and every function and task of the module is resolved again
  // against the complete table (elaborator_items_formals.cpp).
  ResolveModuleClassFormalTypes(mod->class_decls, typedefs_, arena_);
  ResolveModuleSubroutineFormalTypes(decl->items, typedefs_, arena_);

  InstantiateImplicitNestedModules(local_nested_modules, mod);

  // §28.16: a net delay is a property of the net, so it reaches the drivers
  // only once every item is elaborated -- §10.3.2 lets the continuous
  // assignment that drives a net stand before the declaration that gives it its
  // delay, and a gate instance driving it may stand there too.

  RunPostItemValidations(decl, mod);
}

}  // namespace delta
