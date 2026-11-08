#include <cstdint>
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
#include "elaborator/elaborator_node_attributes.h"
#include "elaborator/implication_operator_rules.h"
#include "elaborator/interface_property_instance.h"
#include "elaborator/net_data_type.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

std::optional<std::vector<int64_t>> TryConstEvalInstParams(
    const ModuleItem* item, const ScopeMap& scope) {
  if (item->inst_params.empty()) return std::nullopt;
  std::vector<int64_t> values;
  for (const auto& param : item->inst_params) {
    const Expr* pexpr = param.second;
    if (pexpr == nullptr) return std::nullopt;
    auto v = ConstEvalInt(pexpr, scope);
    if (!v) return std::nullopt;
    values.push_back(*v);
  }
  return values;
}

struct ParentScopeKind {
  bool is_program;
  bool is_checker;
  bool is_interface;
  std::string_view kind_word;
};

struct InstClassTables {
  std::unordered_map<std::string_view, std::string_view>& interface_inst_types;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      interface_inst_param_values;
  std::unordered_set<std::string_view>& checker_inst_names;
  std::unordered_set<std::string_view>& program_inst_names;
};

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

void CheckUdpInstParentRule(const ModuleItem* item, const ModuleDecl* decl,
                            const ParentScopeKind& parent, DiagEngine& diag) {
  const char* subclause = "24.3";
  if (parent.is_interface) {
    subclause = "A.1.6";
  } else if (parent.is_checker) {
    subclause = "A.1.8";
  } else if (!parent.is_program) {
    return;
  }
  diag.Error(item->loc,
             std::format("primitive cannot be instantiated inside "
                         "{} '{}'",
                         parent.kind_word, decl->name),
             Subclause(subclause));
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

bool ModuleExplicitlyInstantiated(const RtlirModule* mod,
                                  std::string_view name) {
  for (const auto& child : mod->children) {
    if (child.module_name == name) return true;
  }
  return false;
}

void CollectNestedModulesAndCheckVif(
    const ModuleDecl* decl,
    std::unordered_map<std::string_view, ModuleDecl*>& nested_module_decls,
    DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl && !item->nested_module_decl->is_extern) {
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

static void DefaultSubroutineLifetime(ModuleItem* item,
                                      bool scope_is_automatic) {
  if ((item->kind != ModuleItemKind::kFunctionDecl &&
       item->kind != ModuleItemKind::kTaskDecl) ||
      !item->method_class.empty() || item->is_automatic || item->is_static) {
    return;
  }
  if (scope_is_automatic) {
    item->is_automatic = true;
  } else {
    item->is_static = true;
  }
}

void DefaultSubroutineLifetimes(const std::vector<ModuleItem*>& items,
                                bool scope_is_automatic) {
  for (auto* item : items) {
    DefaultSubroutineLifetime(item, scope_is_automatic);
    DefaultSubroutineLifetimes(item->gen_body, scope_is_automatic);
    if (item->gen_else != nullptr) {
      DefaultSubroutineLifetimes({item->gen_else}, scope_is_automatic);
    }
    for (const GenerateCaseItem& arm : item->gen_case_items) {
      DefaultSubroutineLifetimes(arm.body, scope_is_automatic);
    }
  }
}

void DefaultTaskFuncLifetimes(const ModuleDecl* decl) {
  DefaultSubroutineLifetimes(decl->items, decl->is_automatic);
}

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

void ClassifyTaskFuncDecls(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    std::unordered_set<std::string_view>& auto_task_func_names) {
  RecordTaskFuncNames(decl, task_names, func_decls);
  DefaultTaskFuncLifetimes(decl);
  CollectAutoTaskFuncNames(decl, auto_task_func_names);
}

struct ItemScopeContext {
  const ParentScopeKind& parent_scope;
  const ScopeMap& scope;
  DiagEngine& diag;
};

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

void RegisterPackageAssertionDecls(const ModuleDecl* decl,
                                   const CompilationUnit* unit,
                                   PropertyRegistry& registry, Arena& arena) {
  if (unit == nullptr) return;
  for (const ModuleItem* item : unit->cu_items) registry.Register(item);
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

bool IsImplicitNestedInstantiationCandidate(std::string_view name,
                                            const ModuleDecl* nested_decl,
                                            const RtlirModule* mod) {
  if (!nested_decl->ports.empty()) return false;
  if (nested_decl->decl_kind == ModuleDeclKind::kInterface) return false;
  if (ModuleExplicitlyInstantiated(mod, name)) return false;
  return true;
}

}  // namespace

void Elaborator::DefaultPackageTaskFuncLifetimes() {
  for (auto* pkg : unit_->packages) {
    DefaultSubroutineLifetimes(pkg->items, pkg->is_automatic);
  }
  DefaultSubroutineLifetimes(unit_->cu_items, false);
}

void Elaborator::RunPostItemValidations(const ModuleDecl* decl,
                                        RtlirModule* mod) {
  CheckAlwaysCombMultiDriver(decl, mod);
  CheckAggregateElementDrivers(decl, mod);
  type_ref_mod_ = mod;
  ValidateModuleConstraints(decl, mod);
  ValidateValueParams(decl, mod);
  const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
  RecordParamDefaultMismatches(*mod, 0, {kTables, BuildParamScope(mod), unit_},
                               arena_);
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
  for (const auto& param : decl->params) {
    ReportImplicationOperators(param.second, diag_);
  }
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
    inst.is_nested_decl = true;
    ParamList empty_params;

    std::string saved_inst_path = current_inst_path_;
    if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
    current_inst_path_.append(name.data(), name.size());
    std::string saved_config_path = std::exchange(
        config_inst_path_, HierInstancePath(config_inst_path_, {}, name));
    BeginNestedDeclScope(nested_decl, CaptureCurrentScopeNames());
    nested_default_disable_iff_ = mod->default_disable_iff;
    nested_default_clock_ = DefaultClockingEvent(mod);
    pending_enclosing_nested_decls_ = NestedDeclsSeenInside();
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    config_inst_path_ = std::move(saved_config_path);
    mod->children.push_back(inst);
  }
}

void Elaborator::ElaborateItemsInOrder(const ModuleDecl* decl,
                                       RtlirModule* mod) {
  RecordNestedDeclNamesAbove(decl->items);
  for (const auto* modport : decl->modports) {
    DeclareInModuleNameSpace(modport->name, modport->loc);
  }
  for (auto* item : decl->items) {
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
  RecordModportAttributes(*mod, diag_, [&] { return BuildParamScope(mod); });
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  ReclassifyForwardUdpInstances(decl);
  CollectNestedModulesAndCheckVif(decl, nested_module_decls_, diag_);
  const bool kParentIsProgram = decl->decl_kind == ModuleDeclKind::kProgram;
  const bool kParentIsChecker = decl->decl_kind == ModuleDeclKind::kChecker;
  const bool kParentIsInterface = decl->decl_kind == ModuleDeclKind::kInterface;
  std::string_view kind_word = "checker";
  if (kParentIsProgram) kind_word = "program";
  if (kParentIsInterface) kind_word = "interface";
  const ParentScopeKind kParentScope{kParentIsProgram, kParentIsChecker,
                                     kParentIsInterface, kind_word};
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

  for (const auto& [pname, pval] : decl->params) {
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
  mod->default_disable_iff = DeclaredDefaultDisableIff(decl->items);
  if (mod->default_disable_iff == nullptr) {
    mod->default_disable_iff = inherited_default_disable_iff_;
  }
  mod->inherited_default_clock = inherited_default_clock_;

  ConstFuncRegistryGuard const_func_guard(&func_decls_);

  std::unordered_map<std::string_view, const ClassDecl*> param_class_registry =
      BuildParamClassRegistry(unit_);
  ParamClassRegistryGuard param_class_guard(&param_class_registry);

  ParamRangeRegistryGuard param_range_guard(mod);
  TypedefRegistryGuard typedef_guard(&typedefs_, &aggregate_typedef_names_,
                                     &type_ref_compare_);
  RegisteredGenScopeGuard gen_scope_guard(gen_prefix_scopes_);

  ElaborateItemsInOrder(decl, mod);

  ResolveModuleClassFormalTypes(mod->class_decls, typedefs_, arena_);
  ResolveModuleSubroutineFormalTypes(decl->items, typedefs_, arena_);

  InstantiateImplicitNestedModules(local_nested_modules, mod);

  RunPostItemValidations(decl, mod);
}

}  // namespace delta
