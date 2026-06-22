#include "elaborator/elaborator.h"

#include <format>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

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

// Copies an AST liblist (string_views into the source) into owning strings.
std::vector<std::string> LiblistToStrings(
    const std::vector<std::string_view>& liblist) {
  std::vector<std::string> libs;
  libs.reserve(liblist.size());
  for (auto lib : liblist) libs.emplace_back(lib);
  return libs;
}

// Finds the configuration named want among configs, excluding self. Returns
// nullptr when no such configuration exists (§33.4.1 config delegation).
const ConfigDecl* FindDelegatedConfig(const std::vector<ConfigDecl*>& configs,
                                      const ConfigDecl* self,
                                      std::string_view want) {
  for (auto* other : configs) {
    if (other != self && other->name == want) return other;
  }
  return nullptr;
}

// True when an inner instance path lies at or beneath the inner config's top
// cell, so it can be rewritten onto the outer hierarchy (§33.4.1).
bool InnerPathUnderTop(std::string_view ipath, std::string_view inner_top) {
  return ipath == inner_top ||
         (ipath.size() > inner_top.size() && ipath.starts_with(inner_top) &&
          ipath[inner_top.size()] == '.');
}

// Records a delegated inner default rule (§33.4.1) as a liblist override rooted
// at outer_path. No-op when the rule carries no library list.
void CollectInnerConfigDefaultOverride(
    const ConfigRule* irule, const std::string& outer_path,
    std::vector<std::pair<std::string, std::vector<std::string>>>& overrides) {
  if (irule->liblist.empty()) return;
  overrides.emplace_back(outer_path, LiblistToStrings(irule->liblist));
}

// Translates a delegated inner instance rule (§33.4.1) whose path lies under
// inner_top into a liblist override rooted at outer_path. No-op when the rule
// carries no library list or its path is outside the inner top cell.
void CollectInnerConfigInstanceOverride(
    const ConfigRule* irule, const std::string& outer_path,
    std::string_view inner_top,
    std::vector<std::pair<std::string, std::vector<std::string>>>& overrides) {
  if (irule->liblist.empty()) return;
  std::string_view ipath = irule->inst_path;
  if (!InnerPathUnderTop(ipath, inner_top)) return;
  std::string translated = outer_path;
  if (ipath.size() > inner_top.size()) {
    translated.append(ipath.substr(inner_top.size()));
  }
  overrides.emplace_back(std::move(translated),
                         LiblistToStrings(irule->liblist));
}

// Translates the default/instance liblist rules of a delegated inner config
// (§33.4.1) into instance liblist overrides rooted at outer_path, appending
// them to overrides. inner_top names the inner config's top cell, used to
// match and rewrite inner instance paths onto the outer hierarchy.
void CollectInnerConfigLiblistOverrides(
    const ConfigDecl* inner, const std::string& outer_path,
    std::string_view inner_top,
    std::vector<std::pair<std::string, std::vector<std::string>>>& overrides) {
  for (auto* irule : inner->rules) {
    if (irule->kind == ConfigRuleKind::kDefault) {
      CollectInnerConfigDefaultOverride(irule, outer_path, overrides);
    } else if (irule->kind == ConfigRuleKind::kInstance) {
      CollectInnerConfigInstanceOverride(irule, outer_path, inner_top,
                                         overrides);
    }
  }
}

// Sorts the compilation-unit items into the design's function/task and let
// declaration lists, preserving source order (§3.12 compilation-unit scope).
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

// Computes the elaborated bit width of each named typedef into widths.
void PopulateTypeWidths(
    const TypedefMap& typedefs,
    std::unordered_map<std::string_view, uint32_t>& widths) {
  for (const auto& [name, dtype] : typedefs) {
    widths[name] = EvalTypeWidth(dtype, typedefs);
  }
}

// True when an instance clause carries a parameter override to record: either
// an explicit override list or an empty "#()" reset-all marker (§33.4.3).
bool RuleCarriesParamOverride(const ConfigRule* rule) {
  return !rule->use_params.empty() || rule->use_param_reset_all;
}

// Evaluates each config localparam (restricted to a literal value, §33.4.3)
// and records it in scope so later overrides may reference earlier ones.
void EvalConfigLocalparams(const ConfigDecl* cfg, ScopeMap& scope) {
  for (const auto& [name, expr] : cfg->local_params) {
    if (!expr) continue;
    if (auto val = ConstEvalInt(expr, scope)) {
      scope[name] = *val;
    }
  }
}

// Applies the configuration's default clause library list (§33.4.1), taking the
// first default rule. order/strict are set only when such a rule is present.
void ApplyConfigDefaultLiblist(const ConfigDecl* cfg,
                               std::vector<std::string>& order, bool& strict) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kDefault) continue;
    order = LiblistToStrings(rule->liblist);
    strict = true;
    break;
  }
}

// Records the instance-clause library lists (§33.4.1.4) as instance liblist
// overrides keyed by their instance path.
void CollectInstanceLiblistOverrides(
    const ConfigDecl* cfg,
    std::vector<std::pair<std::string, std::vector<std::string>>>& overrides) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->liblist.empty()) continue;
    overrides.emplace_back(std::string(rule->inst_path),
                           LiblistToStrings(rule->liblist));
  }
}

// Expands instance clauses that delegate to another configuration (use config,
// §33.4.1) into instance use overrides plus translated liblist overrides.
void CollectConfigDelegationOverrides(
    const ConfigDecl* cfg, const std::vector<ConfigDecl*>& configs,
    DiagEngine& diag,
    std::vector<std::tuple<std::string, std::string, std::string>>&
        use_overrides,
    std::vector<std::pair<std::string, std::vector<std::string>>>&
        liblist_overrides) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!rule->use_config) continue;
    const ConfigDecl* inner = FindDelegatedConfig(configs, cfg, rule->use_cell);
    if (!inner) {
      diag.Error(cfg->range.start,
                 std::format("config '{}' delegates instance '{}' to unknown "
                             "config '{}'",
                             cfg->name, rule->inst_path, rule->use_cell));
      continue;
    }
    if (inner->design_cells.empty()) continue;
    std::string outer_path(rule->inst_path);
    const auto& [inner_lib, inner_cell] = inner->design_cells.front();
    use_overrides.emplace_back(outer_path, std::string(inner_lib),
                               std::string(inner_cell));

    std::string_view inner_top = inner_cell;
    CollectInnerConfigLiblistOverrides(inner, outer_path, inner_top,
                                       liblist_overrides);
  }
}

// Bundles the most recent elaboration-severity details (§20.10.1) plus the
// simulation-blocked flag for transfer onto the elaborated design.
struct DesignMetadata {
  bool simulation_blocked = false;
  std::string last_severity;
  std::string last_severity_msg;
  std::string last_severity_scope;
  SourceLoc last_severity_loc;
};

// Returns the set of top-level module names, used to anchor the §23.10.4.2
// early-resolution ambiguity check.
std::unordered_set<std::string_view> BuildTopModuleNameSet(
    const RtlirDesign* design) {
  std::unordered_set<std::string_view> top_names;
  for (auto* top : design->top_modules) top_names.insert(top->name);
  return top_names;
}

// Copies the compilation unit's packages and class declarations together with
// the captured elaboration metadata onto the finished design.
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
}

// Performs the order-independent data tail of elaboration: computing each
// typedef's bit width and transferring the CU declarations plus the captured
// severity metadata (§20.10.1) onto the finished design.
void FinalizeDesignTail(RtlirDesign* design, const CompilationUnit* unit,
                        const TypedefMap& typedefs,
                        const DesignMetadata& meta) {
  PopulateTypeWidths(typedefs, design->type_widths);
  CopyDesignMetadata(design, unit, meta);
}

}  // namespace

void Elaborator::RunPreElaborationValidations() {
  ValidateNameSpaces();

  ValidateConfigDesignStatements();

  ValidateConfigDefaultClauses();

  ValidateConfigInstanceClauses();

  ValidateConfigCellClauses();

  ValidateConfigPackageBinding();

  ValidateConfigHierarchicalRules();

  ValidateConfigLocalparams();

  ValidateConfigParamOverrides();

  ValidateAnonymousProgramNameSharing();

  ValidateAnonymousProgramHierRefs();

  ValidatePackageItems();

  ValidatePackageReferences();

  ValidatePackageExports();

  ValidateModports();

  ValidateSpecifyBlocks();

  RegisterCuScopeItems();

  ApplyClassMethodAutomaticDefault();

  ValidateFinalClassExtension();

  ValidateWeakReferenceMembers();

  ValidateChainingConstructors();

  ValidateEmbeddedCovergroupAssign();

  ValidateDerivedCovergroupBase();

  ValidateConstClassProperties();

  ValidateVirtualMethodOverrides();

  ValidateAbstractClassRules();

  ValidateOutOfBlockDeclarations();

  ValidateInterfaceClassRules();

  ValidateRandomVariableTypes();

  ValidateConstraintBlockNames();

  ValidateForeachConstraintDims();

  ValidateSolveBeforeConstraints();

  ValidateSoftConstraintVariables();

  ValidateConstraintFunctionArgs();

  ValidateBuiltinRandomizationMethods();

  ValidateExternalConstraints();

  ValidateConstraintInheritance();

  ValidateForwardClassTypedefs();

  ValidateTimescaleConsistency();

  ValidateDpiDeclarations();

  ValidateDpiGlobalNameSpace();

  ResolveExternModules();
}

bool Elaborator::ElaborateTopModules(const std::vector<ModuleDecl*>& top_decls,
                                     RtlirDesign* design) {
  ParamList empty_params;
  for (auto* mod_decl : top_decls) {
    std::string saved_path = std::move(current_inst_path_);
    current_inst_path_.assign(mod_decl->name.data(), mod_decl->name.size());
    auto* top = ElaborateModule(mod_decl, empty_params);
    current_inst_path_ = std::move(saved_path);
    if (!top) return false;
    design->top_modules.push_back(top);
  }
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
    for (auto& pg : batch) {
      ProcessPendingGenerate(pg.item, pg.mod);
    }
  }
  VerifyEarlyResolvedDefparams();
}

RtlirDesign* Elaborator::ElaborateTops(
    const std::vector<ModuleDecl*>& top_decls) {
  auto* design = arena_.Create<RtlirDesign>();
  pending_generates_.clear();
  applied_defparams_.clear();
  early_defparam_resolutions_.clear();

  if (!ElaborateTopModules(top_decls, design)) return nullptr;

  ResolveDefparamsAndGenerates(design);

  for (auto* top : design->top_modules) {
    WarnUnresolvedDefparams(top);

    ApplyBindDirectives(top);

    ValidateModportExportConflicts(top);

    CollectAllModules(top, design->all_modules);
  }

  // §23.10.4.2: detect defparam hierarchical names whose early resolution would
  // diverge from the fully elaborated hierarchy. all_modules holds each
  // instantiated module once, so each module's defparams are checked a single
  // time regardless of how many instances exist.
  {
    std::unordered_set<std::string_view> top_names =
        BuildTopModuleNameSet(design);
    for (const auto& entry : design->all_modules)
      CheckEarlyResolutionAmbiguity(entry.second, top_names);
  }

  ClassifyCuItems(unit_->cu_items, design->cu_function_decls,
                  design->cu_let_decls);
  for (auto* item : design->cu_let_decls) {
    ValidateLetDecl(item);
  }

  FinalizeDesignTail(
      design, unit_, typedefs_,
      DesignMetadata{elab_simulation_blocked_, elab_last_severity_,
                     elab_last_severity_msg_, elab_last_severity_scope_,
                     elab_last_severity_loc_});
  return design;
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  // No explicit top module: a package-only or class-only compilation unit has
  // nothing to instantiate, but its package/class items still need validation.
  // A genuinely empty unit (e.g. empty/comment-only source) yields no design.
  if (top_module_name.empty()) {
    if (unit_->modules.empty() && unit_->packages.empty() &&
        unit_->cu_items.empty())
      return nullptr;
    RunPreElaborationValidations();
    return ElaborateTops({});
  }

  RunPreElaborationValidations();

  auto* mod_decl = FindModule(top_module_name);
  if (!mod_decl) {
    diag_.Error({}, std::format("top module '{}' not found", top_module_name));
    return nullptr;
  }
  return ElaborateTops({mod_decl});
}

void Elaborator::SetLibraryDeclarationOrder(std::vector<std::string> order) {
  library_order_ = std::move(order);
}

RtlirDesign* Elaborator::Elaborate(const ConfigDecl* cfg) {
  in_config_elaboration_ = true;
  RunPreElaborationValidations();

  // A config localparam is restricted to a literal value (§33.4.3), so it can
  // be evaluated once here and made available to parameter-override
  // expressions that reference it.
  EvalConfigLocalparams(cfg, config_localparam_scope_);

  // Record the parameter overrides each instance clause carries so they can be
  // applied as the matching instance is elaborated (§33.4.3).
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!RuleCarriesParamOverride(rule)) continue;
    ConfigParamOverride ov;
    ov.inst_path.assign(rule->inst_path.data(), rule->inst_path.size());
    ov.reset_all = rule->use_param_reset_all;
    ov.params = rule->use_params;
    instance_param_overrides_.push_back(std::move(ov));
  }

  ApplyConfigDefaultLiblist(cfg, library_order_, library_order_strict_);

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kCell) continue;
    // A cell clause carrying a use expansion rebinds a cell. A target cell is
    // required; the target library may be omitted, in which case it is
    // inherited from the parent cell (§33.4.1.6). The qualifying library, when
    // present, scopes which instances the clause applies to (§33.4.1.4).
    if (!rule->use_cell.empty()) {
      cell_clause_use_overrides_[std::string(rule->cell_name)] = {
          std::string(rule->cell_lib), std::string(rule->use_lib),
          std::string(rule->use_cell)};
      continue;
    }
    // Otherwise the cell clause selects a library list to search for the named
    // cell (§33.4.1.4 selecting the list of §33.4.1.5).
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        LiblistToStrings(rule->liblist);
  }

  CollectInstanceLiblistOverrides(cfg, instance_liblist_overrides_);

  CollectConfigDelegationOverrides(cfg, unit_->configs, diag_,
                                   instance_use_overrides_,
                                   instance_liblist_overrides_);

  std::vector<ModuleDecl*> top_decls;
  top_decls.reserve(cfg->design_cells.size());
  for (const auto& [lib, cell] : cfg->design_cells) {
    auto* md = FindModule(cell);
    if (!md) {
      diag_.Error({}, std::format("config '{}' design cell '{}' not found",
                                  cfg->name, cell));
      return nullptr;
    }
    top_decls.push_back(md);
  }
  return ElaborateTops(top_decls);
}

}  // namespace delta
