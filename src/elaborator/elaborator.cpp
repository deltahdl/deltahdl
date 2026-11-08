#include "elaborator/elaborator.h"

#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/data_declared_before_use.h"
#include "elaborator/elaborator_child_type_params.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_node_attributes.h"
#include "elaborator/elaborator_type_facts.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/net_data_type.h"
#include "elaborator/package_assertion_scope.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/pending_generate.h"
#include "elaborator/rtlir.h"
#include "elaborator/sdf_annotate_calls.h"
#include "elaborator/time_literal_scale.h"
#include "elaborator/unit_hier_names_from_root.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/unit_scope_switch.h"
#include "elaborator/viewport_resolution.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/time_resolve.h"

namespace delta {

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena,
                       const ScopeMap& scope);

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : ElaboratorClassRules(arena, diag, unit) {}

static void CollectAllModules(
    RtlirModule* mod,
    std::unordered_map<std::string_view, RtlirModule*>& all_modules) {
  if (!mod) return;
  auto [it, inserted] = all_modules.try_emplace(mod->name, mod);
  if (!inserted) return;
  for (auto& child : mod->children) {
    CollectAllModules(child.resolved, all_modules);
  }
}

namespace {

void CollectItemInstantiations(const ModuleItem* item,
                               std::vector<InstantiatedCell>& cells) {
  if (item->kind == ModuleItemKind::kModuleInst) {
    if (!item->inst_module.empty())
      cells.push_back({item->inst_module, item->loc});
    return;
  }
  if (item->kind == ModuleItemKind::kNestedModuleDecl) {
    if (item->nested_module_decl != nullptr)
      CollectInstantiations(item->nested_module_decl->items, cells);
    return;
  }
  CollectInstantiations(item->gen_body, cells);
  if (item->gen_else != nullptr)
    CollectItemInstantiations(item->gen_else, cells);
  for (const auto& ci : item->gen_case_items)
    CollectInstantiations(ci.body, cells);
}

void CollectBoundNames(const std::vector<BindDirective*>& binds,
                       std::unordered_set<std::string_view>& names) {
  for (const auto* bd : binds) {
    if (bd != nullptr && bd->instantiation != nullptr) {
      names.insert(bd->instantiation->inst_module);
    }
  }
}

std::vector<ModuleDecl*> CollectAutoTopModules(const CompilationUnit* unit) {
  std::unordered_set<std::string_view> instantiated;
  for (const auto* mod : unit->modules) {
    CollectInstantiatedNames(mod->items, instantiated);
    CollectBoundNames(mod->bind_directives, instantiated);
  }
  for (const auto* prog : unit->programs)
    CollectInstantiatedNames(prog->items, instantiated);
  for (const auto* iface : unit->interfaces) {
    CollectInstantiatedNames(iface->items, instantiated);
    CollectBoundNames(iface->bind_directives, instantiated);
  }
  CollectBoundNames(unit->bind_directives, instantiated);

  std::vector<ModuleDecl*> tops;
  for (auto* mod : unit->modules)
    if (!instantiated.contains(mod->name)) tops.push_back(mod);
  for (auto* prog : unit->programs)
    if (!prog->is_extern && !instantiated.contains(prog->name))
      tops.push_back(prog);
  return tops;
}

std::vector<std::string> LiblistToStrings(
    const std::vector<std::string_view>& liblist) {
  std::vector<std::string> libs;
  libs.reserve(liblist.size());
  for (auto lib : liblist) libs.emplace_back(lib);
  return libs;
}

const ConfigDecl* FindDelegatedConfig(const std::vector<ConfigDecl*>& configs,
                                      const ConfigDecl* self,
                                      std::string_view want) {
  for (auto* other : configs) {
    if (other != self && other->name == want) return other;
  }
  return nullptr;
}

}  // namespace

void CollectInstantiations(const std::vector<ModuleItem*>& items,
                           std::vector<InstantiatedCell>& cells) {
  for (const auto* item : items) CollectItemInstantiations(item, cells);
}

void CollectInstantiatedNames(const std::vector<ModuleItem*>& items,
                              std::unordered_set<std::string_view>& names) {
  std::vector<InstantiatedCell> cells;
  CollectInstantiations(items, cells);
  for (const auto& cell : cells) names.insert(cell.name);
}

bool UseClauseNamesConfig(const ConfigRule* rule, const ConfigDecl* cfg,
                          const CompilationUnit* unit) {
  if (rule->use_config) return true;
  if (rule->use_cell.empty()) return false;
  if (NonConfigCellNames(unit).contains(rule->use_cell)) return false;
  return FindDelegatedConfig(unit->configs, cfg, rule->use_cell) != nullptr;
}

namespace {

std::string_view ConfigLibCell(const ConfigDecl* cfg, Arena& arena) {
  const std::string kName =
      std::string(cfg->library) + "." + std::string(cfg->name);
  return {arena.AllocString(kName.c_str(), kName.size()), kName.size()};
}

bool RebaseConfigPath(std::string& path, std::string_view inner_top,
                      std::string_view outer_path) {
  const bool kUnder = path == inner_top || (path.size() > inner_top.size() &&
                                            path.starts_with(inner_top) &&
                                            path[inner_top.size()] == '.');
  if (!kUnder) return false;
  path = std::string(outer_path) + path.substr(inner_top.size());
  return true;
}

template <typename Table, typename PathOf>
void RebaseConfigTable(Table& table, std::string_view inner_top,
                       std::string_view outer_path, PathOf path_of) {
  std::erase_if(table, [&](auto& entry) {
    return !RebaseConfigPath(path_of(entry), inner_top, outer_path);
  });
}

void ClassifyCuItems(const std::vector<ModuleItem*>& cu_items,
                     std::vector<ModuleItem*>& function_decls,
                     std::vector<ModuleItem*>& let_decls) {
  for (auto* item : cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      function_decls.push_back(item);
    } else if (item->kind == ModuleItemKind::kLetDecl) {
      let_decls.push_back(item);
    }
  }
}

bool RuleCarriesParamOverride(const ConfigRule* rule) {
  return !rule->use_params.empty() || rule->use_param_reset_all;
}

void EvalConfigLocalparams(const ConfigDecl* cfg, ScopeMap& scope) {
  for (const ConfigLocalparam& lp : cfg->local_params) {
    if (lp.is_type || lp.init_expr == nullptr) continue;
    auto val = FoldDeclaredParamValue(lp.init_expr, lp.data_type, scope);
    if (val) scope[lp.name] = *val;
  }
}

bool HoldsItsLiteralAsWritten(const ConfigLocalparam& lp) {
  return !lp.is_type && lp.init_expr != nullptr &&
         IsLiteralKind(lp.init_expr->kind) &&
         lp.data_type.kind == DataTypeKind::kImplicit &&
         lp.data_type.packed_dim_left == nullptr;
}

void ApplyConfigDefaultLiblist(const ConfigDecl* cfg,
                               std::vector<std::string>& order, bool& strict) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kDefault) continue;
    order = LiblistToStrings(rule->liblist);
    strict = true;
    break;
  }
}

void CollectInstanceLiblistOverrides(
    const ConfigDecl* cfg,
    std::vector<std::pair<std::string, std::vector<std::string>>>& overrides) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    const bool kUseExpansion = !rule->use_cell.empty() ||
                               !rule->use_lib.empty() || rule->use_config ||
                               RuleCarriesParamOverride(rule);
    if (kUseExpansion) continue;
    overrides.emplace_back(std::string(rule->inst_path),
                           LiblistToStrings(rule->liblist));
  }
}

void CollectConfigDelegationOverrides(
    const ConfigDecl* cfg, const CompilationUnit* unit, DiagEngine& diag,
    std::vector<std::tuple<std::string, std::string, std::string>>&
        use_overrides,
    std::vector<std::pair<std::string, const ConfigDecl*>>& delegations) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!UseClauseNamesConfig(rule, cfg, unit)) continue;
    const ConfigDecl* inner =
        FindDelegatedConfig(unit->configs, cfg, rule->use_cell);
    if (!inner) {
      diag.Error(rule->loc,
                 std::format("config '{}' delegates instance '{}' to unknown "
                             "config '{}'",
                             cfg->name, rule->inst_path, rule->use_cell),
                 Subclause("33.4.2"));
      continue;
    }
    if (inner->design_cells.empty()) continue;
    std::string outer_path(rule->inst_path);
    const ConfigDesignCell& inner_first = inner->design_cells.front();
    use_overrides.emplace_back(outer_path, std::string(inner_first.library),
                               std::string(inner_first.cell));
    delegations.emplace_back(std::move(outer_path), inner);
  }
}

struct DesignMetadata {
  bool simulation_blocked = false;
  std::string last_severity;
  std::string last_severity_msg;
  std::string last_severity_scope;
  SourceLoc last_severity_loc;
};

std::unordered_set<std::string_view> BuildTopModuleNameSet(
    const RtlirDesign* design) {
  std::unordered_set<std::string_view> top_names;
  for (auto* top : design->top_modules) top_names.insert(top->name);
  return top_names;
}

void CopyDesignMetadata(RtlirDesign* design, const CompilationUnit* unit,
                        const DesignMetadata& meta) {
  design->packages = unit->packages;
  design->cu_class_decls.insert(design->cu_class_decls.end(),
                                unit->classes.begin(), unit->classes.end());
  design->simulation_blocked = meta.simulation_blocked;
  design->last_elab_severity = meta.last_severity;
  design->last_elab_severity_msg = meta.last_severity_msg;
  design->last_elab_severity_scope = meta.last_severity_scope;
  design->last_elab_severity_loc = meta.last_severity_loc;

  design->cu_timescale = CompilationUnitTimescale(*unit);
  design->global_time_precision = ComputeGlobalTimePrecision(
      unit, unit->has_preproc_global_precision, unit->preproc_global_precision);
  design->global_precision_order = GlobalTimePrecisionOrder(unit);
}

void FinalizeDesignTail(RtlirDesign* design, const CompilationUnit* unit,
                        const TypeNameSources& src,
                        const DesignMetadata& meta) {
  TypeNameFacts facts{design->type_widths,  design->type_kinds,
                      design->type_signed,  design->type_layouts,
                      design->type_targets, design->type_ranges,
                      design->type_enums,   design->type_interfaces};
  PopulateTypeWidths(src, facts);
  CopyDesignMetadata(design, unit, meta);
}

std::string DesignCellNotFoundMessage(std::string_view config_name,
                                      std::string_view library,
                                      std::string_view cell, bool confined) {
  if (!confined) {
    return std::format("config '{}' design cell '{}' not found", config_name,
                       cell);
  }
  return std::format("config '{}' design cell '{}' not found in library '{}'",
                     config_name, cell, library);
}

}  // namespace

void Elaborator::RunPreElaborationValidations() {
  BreakClassInheritanceCycles();

  ValidateNameSpaces();

  ValidateConfigDesignStatements();
  ValidateConfigDefaultClauses();

  ValidateConfigInstanceClauses();

  ValidateConfigCellClauses();

  ValidateConfigPackageBinding();
  ValidateConfigHierarchicalRules();

  ValidateConfigLocalparams();
  ValidateConfigParamOverrides();

  UnitScopeTables::ForEachUnit(
      *this, [this] { ValidateAnonymousProgramNameSharing(); });

  ValidateAnonymousProgramHierRefs();

  ValidatePackageItems();
  ReportDataUsedAboveItsDeclaration(*unit_, diag_);
  ReportReferencesBeforePackages(unit_, diag_);
  ValidatePackageReferences();

  ValidatePackageExports();

  ValidateModports();

  ValidateSpecifyBlocks();

  ReportViewportsContainingNothing(*unit_, diag_);

  RegisterCuScopeItems();

  ValidateProgramWideSpaceAccessInPackageAndCuScopes();

  ValidateCuTypedefs();

  ApplyClassMethodAutomaticDefault();

  DefaultPackageTaskFuncLifetimes();

  ResolvePackageAssertionNames(unit_, arena_);

  ValidatePackageCycleDelays(unit_, diag_);

  ValidatePackageValueParams();

  const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
  ReportUnitParamValueTypes({kTables, cu_param_scope_, unit_}, diag_);

  RunPreElaborationClassValidations();

  ValidatePerDeclarationRulesInUnitScopes();

  ValidateUnitConstAssignments();

  ValidateTimescaleConsistency();

  UnitScopeTables::ForEachUnit(*this, [this] { ValidateTimescaleOrder(); });

  ValidateDpiDeclarations();

  ValidateDpiGlobalNameSpace();

  ResolveExternModules();
}

bool Elaborator::ElaborateTopModules(const std::vector<ModuleDecl*>& top_decls,
                                     RtlirDesign* design) {
  for (auto* mod_decl : top_decls) {
    std::string saved_path = std::move(current_inst_path_);
    current_inst_path_.assign(mod_decl->name.data(), mod_decl->name.size());
    std::string saved_config_path =
        std::exchange(config_inst_path_, current_inst_path_);
    ParamList top_params;
    std::vector<std::string_view> config_locked;
    ModuleItem top_item;
    top_item.inst_module = mod_decl->name;
    ApplyConfigParamOverrides(&top_item, mod_decl, top_params, cu_param_scope_,
                              config_locked);
    AppliedTypeParams applied_type_params;
    if (AllTypeParamsHaveDefaults(mod_decl)) {
      applied_type_params = ApplyChildTypeParams(
          TypeParamSourcesFor(&top_item, instance_param_overrides_,
                              config_inst_path_),
          mod_decl, typedefs_, unit_, diag_);
      ReportChildTypeParamsOutsideRestrictions(mod_decl, applied_type_params,
                                               {typedefs_, unit_, class_names_},
                                               diag_);
    }
    pending_type_param_types_ = std::move(applied_type_params.written);
    auto* top = ElaborateModule(mod_decl, top_params);
    RestoreChildTypeParams(typedefs_, applied_type_params.saved);
    current_inst_path_ = std::move(saved_path);
    config_inst_path_ = std::move(saved_config_path);
    if (!top) return false;
    for (auto& p : top->params) {
      if (std::ranges::find(config_locked, p.name) != config_locked.end()) {
        p.config_locked = true;
      }
    }
    design->top_modules.push_back(top);
  }
  typedefs_ = all_typedefs_;
  cu_param_scope_ = all_cu_param_scope_;
  td_array_dims_ = all_td_array_dims_;
  return true;
}

void Elaborator::ResolveDefparamsAndGenerates(RtlirDesign* design) {
  while (true) {
    for (auto* top : design->top_modules) {
      ApplyDefparamsRecursively(top);
    }
    if (pending_generates_.empty()) break;
    std::vector<PendingGenerate> batch;
    batch.swap(pending_generates_);
    for (const auto& pg : batch) {
      ProcessPendingGenerate(pg);
    }
  }
}

RtlirDesign* Elaborator::ElaborateTops(
    const std::vector<ModuleDecl*>& top_decls) {
  auto* design = arena_.Create<RtlirDesign>();
  design->compilation_unit = unit_;
  design->compilation_units = units_.units;
  design->top_decls.assign(top_decls.begin(), top_decls.end());
  top_decls_ = design->top_decls;
  ResetPendingElaboration();
  ConstFuncSeverityGuard severity_guard(diag_, arena_);

  if (!ElaborateTopModules(top_decls, design)) return nullptr;

  defparam_top_roots_ = design->top_modules;
  ResolveDefparamsAndGenerates(design);

  for (auto* top : design->top_modules) WarnUnresolvedDefparams(top);
  ApplyBindDirectives(design->top_modules);
  while (!pending_generates_.empty()) {
    std::vector<PendingGenerate> batch;
    batch.swap(pending_generates_);
    for (const auto& pg : batch) ProcessPendingGenerate(pg);
  }

  for (const auto* top : design->top_modules)
    ReportParamDefaultMismatches(*top, diag_);
  for (auto* top : design->top_modules) {
    ValidateModportExportConflicts(top);
    CollectAllModules(top, design->all_modules);
  }
  ReportUnitHierNamesFromRoot(*unit_, *design, pkg_provided_names_, diag_);
  ReportHierNamesReachingTheUnit(*unit_, *design, diag_);
  WarnUwireNetsKeptApart(*design, diag_);
  interconnect_merges_.Resolve(diag_);

  {
    std::unordered_set<std::string_view> top_names =
        BuildTopModuleNameSet(design);
    for (const auto& entry : design->all_modules)
      CheckEarlyResolutionAmbiguity(entry.second, top_names);
  }

  ClassifyCuItems(unit_->cu_items, design->cu_function_decls,
                  design->cu_let_decls);

  design->unit_constants = cu_param_scope_;
  design->unit_type_ref_compares = std::move(unit_type_ref_compares_);
  FinalizeDesignTail(
      design, unit_,
      TypeNameSources{typedefs_, aggregate_typedef_names_, arena_},
      DesignMetadata{elab_simulation_blocked_, elab_last_severity_,
                     elab_last_severity_msg_, elab_last_severity_scope_,
                     elab_last_severity_loc_});
  RecordDesignAttributes(*design, diag_, cu_param_scope_);
  UnitScopeTables::PopulateUnitTypeFacts(*this, design);
  return design;
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  if (top_module_name.empty()) {
    if (unit_->DeclaresNothing()) return nullptr;
    UnitScopeTables::RunPreElaborationValidations(*this);
    auto tops = CollectAutoTopModules(unit_);
    if (tops.empty() && !unit_->modules.empty()) {
      diag_.Error(SourceLoc::None(), "design contains no top-level module",
                  Subclause("23.3.1"));
      return nullptr;
    }
    return ElaborateTops(tops);
  }

  UnitScopeTables::RunPreElaborationValidations(*this);

  auto* mod_decl = FindModule(top_module_name);
  if (!mod_decl) {
    diag_.Error(SourceLoc::None(),
                std::format("top module '{}' not found", top_module_name),
                Subclause::None());
    return nullptr;
  }
  return ElaborateTops({mod_decl});
}

RtlirDesign* Elaborator::Elaborate(
    const std::vector<std::string_view>& top_names) {
  if (top_names.empty()) {
    diag_.Error(SourceLoc::None(), "no top-level module was named to elaborate",
                Subclause::None());
    return nullptr;
  }

  UnitScopeTables::RunPreElaborationValidations(*this);

  std::vector<ModuleDecl*> tops;
  tops.reserve(top_names.size());
  std::unordered_set<std::string_view> already_named;
  for (auto name : top_names) {
    if (!already_named.insert(name).second) continue;
    const auto& [lib, cell] = SplitLibCell(name);
    auto* mod_decl = FindDesignCell(lib, cell);
    if (mod_decl == nullptr) {
      diag_.Error(SourceLoc::None(),
                  std::format("top module '{}' not found", name),
                  Subclause::None());
      return nullptr;
    }
    tops.push_back(mod_decl);
  }
  return ElaborateTops(tops);
}

void Elaborator::SetLibraryDeclarationOrder(std::vector<std::string> order) {
  library_order_ = std::move(order);
}

void Elaborator::SetMaxGenerateIterations(int64_t max_iterations) {
  max_generate_iterations_ = max_iterations;
}

static std::vector<std::pair<std::string_view, Expr*>>
OverridesWithLocalparamLiterals(
    const ConfigDecl* cfg,
    std::vector<std::pair<std::string_view, Expr*>> params) {
  for (auto& [pname, pexpr] : params) {
    if (pexpr == nullptr || pexpr->kind != ExprKind::kIdentifier) continue;
    for (const ConfigLocalparam& lp : cfg->local_params) {
      if (lp.name == pexpr->text && HoldsItsLiteralAsWritten(lp)) {
        pexpr = lp.init_expr;
        break;
      }
    }
  }
  return params;
}

static void FillRuleParamOverride(auto& ov, const ConfigDecl* cfg,
                                  const ConfigRule* rule,
                                  std::string_view path) {
  ov.inst_path.assign(path.data(), path.size());
  ov.reset_all = rule->use_param_reset_all;
  ov.loc = rule->loc;
  ov.params = OverridesWithLocalparamLiterals(cfg, rule->use_params);
}

static bool CellUseTarget(const ConfigRule* rule, const ConfigDecl* cfg,
                          const CompilationUnit* unit, std::string& use_lib,
                          std::string& use_cell) {
  use_lib = std::string(rule->use_lib);
  use_cell = std::string(rule->use_cell);
  if (!UseClauseNamesConfig(rule, cfg, unit)) return true;
  const ConfigDecl* inner =
      FindDelegatedConfig(unit->configs, cfg, rule->use_cell);
  if (inner == nullptr || inner->design_cells.empty()) return false;
  const ConfigDesignCell& design = inner->design_cells.front();
  use_lib = design.library.empty() ? std::string(inner->library)
                                   : std::string(design.library);
  use_cell = std::string(design.cell);
  return true;
}

void Elaborator::CollectConfigInstanceParamOverrides(const ConfigDecl* cfg) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!RuleCarriesParamOverride(rule)) continue;
    FillRuleParamOverride(instance_param_overrides_.emplace_back(), cfg, rule,
                          rule->inst_path);
  }
}

void Elaborator::CollectCellUseOverride(const ConfigDecl* cfg,
                                        const ConfigRule* rule) {
  std::string use_lib;
  std::string use_cell;
  if (!CellUseTarget(rule, cfg, unit_, use_lib, use_cell)) return;
  if (UseClauseNamesConfig(rule, cfg, unit_)) {
    cell_config_delegations_[std::string(rule->cell_name)] =
        FindDelegatedConfig(unit_->configs, cfg, rule->use_cell);
  }
  cell_clause_use_overrides_[std::string(rule->cell_name)] = {
      std::string(rule->cell_lib), std::move(use_lib), std::move(use_cell)};
}

void Elaborator::CollectConfigCellClauseOverrides(const ConfigDecl* cfg) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kCell) continue;
    if (RuleCarriesParamOverride(rule)) {
      FillRuleParamOverride(cell_param_overrides_.emplace_back(), cfg, rule,
                            rule->cell_name);
      if (rule->use_cell.empty()) continue;
    }
    if (!rule->use_cell.empty()) {
      CollectCellUseOverride(cfg, rule);
      continue;
    }
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        LiblistToStrings(rule->liblist);
  }
}

void Elaborator::CollectConfigInstanceBindOverrides(const ConfigDecl* cfg) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance || rule->use_cell.empty() ||
        UseClauseNamesConfig(rule, cfg, unit_)) {
      continue;
    }
    instance_bind_overrides_.emplace_back(std::string(rule->inst_path),
                                          std::string(rule->use_lib),
                                          std::string(rule->use_cell));
  }
}

const ConfigDecl* Elaborator::DelegatedConfigFor(std::string_view cell) const {
  for (const auto& [path, inner] : config_delegations_) {
    if (path == config_inst_path_) return inner;
  }
  auto it = cell_config_delegations_.find(std::string(cell));
  return it == cell_config_delegations_.end() ? nullptr : it->second;
}

void Elaborator::EnterDelegatedConfig(const ConfigDecl* inner) {
  enclosing_config_rules_.push_back(
      {std::move(library_order_), library_order_strict_,
       std::move(cell_clause_use_overrides_),
       std::move(cell_clause_liblist_overrides_),
       std::move(instance_liblist_overrides_),
       std::move(instance_use_overrides_), std::move(instance_bind_overrides_),
       std::move(instance_param_overrides_), std::move(cell_param_overrides_),
       std::move(config_localparam_scope_), std::move(cell_liblist_bindings_),
       std::move(config_delegations_), std::move(cell_config_delegations_),
       active_config_});
  active_config_ = ConfigLibCell(inner, arena_);
  library_order_ = enclosing_config_rules_.back().library_order;
  library_order_strict_ = false;
  cell_clause_use_overrides_.clear();
  cell_clause_liblist_overrides_.clear();
  instance_liblist_overrides_.clear();
  instance_use_overrides_.clear();
  instance_bind_overrides_.clear();
  instance_param_overrides_.clear();
  cell_param_overrides_.clear();
  config_localparam_scope_.clear();
  cell_liblist_bindings_.clear();
  config_delegations_.clear();
  cell_config_delegations_.clear();
  EvalConfigLocalparams(inner, config_localparam_scope_);
  CollectConfigRuleTables(inner);
  CollectConfigInstanceParamOverrides(inner);
  const std::string_view kTop = inner->design_cells.front().cell;
  const std::string_view kAt = config_inst_path_;
  RebaseConfigTable(instance_liblist_overrides_, kTop, kAt,
                    [](auto& e) -> std::string& { return e.first; });
  RebaseConfigTable(instance_use_overrides_, kTop, kAt,
                    [](auto& e) -> std::string& { return std::get<0>(e); });
  RebaseConfigTable(instance_bind_overrides_, kTop, kAt,
                    [](auto& e) -> std::string& { return std::get<0>(e); });
  RebaseConfigTable(instance_param_overrides_, kTop, kAt,
                    [](auto& e) -> std::string& { return e.inst_path; });
  RebaseConfigTable(config_delegations_, kTop, kAt,
                    [](auto& e) -> std::string& { return e.first; });
}

void Elaborator::LeaveDelegatedConfig() {
  ConfigRuleTables& outer = enclosing_config_rules_.back();
  library_order_ = std::move(outer.library_order);
  library_order_strict_ = outer.library_order_strict;
  cell_clause_use_overrides_ = std::move(outer.cell_uses);
  cell_clause_liblist_overrides_ = std::move(outer.cell_liblists);
  instance_liblist_overrides_ = std::move(outer.instance_liblists);
  instance_use_overrides_ = std::move(outer.instance_uses);
  instance_bind_overrides_ = std::move(outer.instance_binds);
  instance_param_overrides_ = std::move(outer.instance_params);
  cell_param_overrides_ = std::move(outer.cell_params);
  config_localparam_scope_ = std::move(outer.localparams);
  cell_liblist_bindings_ = std::move(outer.cell_liblist_bindings);
  config_delegations_ = std::move(outer.delegations);
  cell_config_delegations_ = std::move(outer.cell_delegations);
  active_config_ = outer.config;
  enclosing_config_rules_.pop_back();
}

void Elaborator::CollectConfigRuleTables(const ConfigDecl* cfg) {
  ApplyConfigDefaultLiblist(cfg, library_order_, library_order_strict_);
  CollectConfigCellClauseOverrides(cfg);
  CollectInstanceLiblistOverrides(cfg, instance_liblist_overrides_);
  CollectConfigDelegationOverrides(cfg, unit_, diag_, instance_use_overrides_,
                                   config_delegations_);
  CollectConfigInstanceBindOverrides(cfg);
}

RtlirDesign* Elaborator::Elaborate(const ConfigDecl* cfg) {
  in_config_elaboration_ = true;
  active_config_ = ConfigLibCell(cfg, arena_);

  UnitScopeTables::RunPreElaborationValidations(*this);

  EvalConfigLocalparams(cfg, config_localparam_scope_);

  CollectConfigInstanceParamOverrides(cfg);

  std::vector<ModuleDecl*> top_decls;
  top_decls.reserve(cfg->design_cells.size());
  for (const ConfigDesignCell& design_cell : cfg->design_cells) {
    auto* md = FindDesignCell(design_cell.library, design_cell.cell);
    if (!md) {
      auto msg = DesignCellNotFoundMessage(cfg->name, design_cell.library,
                                           design_cell.cell,
                                           !design_cell.library.empty());
      diag_.Error(design_cell.loc, msg, Subclause("33.4.1.1"));
      return nullptr;
    }
    top_decls.push_back(md);
  }

  CollectConfigRuleTables(cfg);

  return ElaborateTops(top_decls);
}

}  // namespace delta
