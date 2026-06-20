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

RtlirDesign* Elaborator::ElaborateTops(
    const std::vector<ModuleDecl*>& top_decls) {
  auto* design = arena_.Create<RtlirDesign>();
  ParamList empty_params;
  pending_generates_.clear();
  applied_defparams_.clear();
  early_defparam_resolutions_.clear();

  for (auto* mod_decl : top_decls) {
    std::string saved_path = std::move(current_inst_path_);
    current_inst_path_.assign(mod_decl->name.data(), mod_decl->name.size());
    auto* top = ElaborateModule(mod_decl, empty_params);
    current_inst_path_ = std::move(saved_path);
    if (!top) return nullptr;
    design->top_modules.push_back(top);
  }

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
    std::unordered_set<std::string_view> top_names;
    for (auto* top : design->top_modules) top_names.insert(top->name);
    for (const auto& entry : design->all_modules)
      CheckEarlyResolutionAmbiguity(entry.second, top_names);
  }

  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      design->cu_function_decls.push_back(item);
    } else if (item->kind == ModuleItemKind::kLetDecl) {
      ValidateLetDecl(item);
      design->cu_let_decls.push_back(item);
    }
  }

  for (const auto& [name, dtype] : typedefs_) {
    design->type_widths[name] = EvalTypeWidth(dtype, typedefs_);
  }

  design->packages = unit_->packages;

  design->cu_class_decls.insert(design->cu_class_decls.end(),
                                unit_->classes.begin(), unit_->classes.end());
  design->simulation_blocked = elab_simulation_blocked_;
  design->last_elab_severity = elab_last_severity_;
  design->last_elab_severity_msg = elab_last_severity_msg_;
  design->last_elab_severity_scope = elab_last_severity_scope_;
  design->last_elab_severity_loc = elab_last_severity_loc_;
  return design;
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
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
  for (const auto& [name, expr] : cfg->local_params) {
    if (!expr) continue;
    if (auto val = ConstEvalInt(expr, config_localparam_scope_)) {
      config_localparam_scope_[name] = *val;
    }
  }

  // Record the parameter overrides each instance clause carries so they can be
  // applied as the matching instance is elaborated (§33.4.3).
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->use_params.empty() && !rule->use_param_reset_all) continue;
    ConfigParamOverride ov;
    ov.inst_path.assign(rule->inst_path.data(), rule->inst_path.size());
    ov.reset_all = rule->use_param_reset_all;
    ov.params = rule->use_params;
    instance_param_overrides_.push_back(std::move(ov));
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kDefault) continue;
    library_order_.clear();
    library_order_.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) {
      library_order_.emplace_back(lib);
    }
    library_order_strict_ = true;
    break;
  }

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
    std::vector<std::string> libs;
    libs.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) libs.emplace_back(lib);
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        std::move(libs);
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->liblist.empty()) continue;
    std::vector<std::string> libs;
    libs.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) libs.emplace_back(lib);
    instance_liblist_overrides_.emplace_back(std::string(rule->inst_path),
                                             std::move(libs));
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!rule->use_config) continue;
    const ConfigDecl* inner = nullptr;
    for (auto* other : unit_->configs) {
      if (other != cfg && other->name == rule->use_cell) {
        inner = other;
        break;
      }
    }
    if (!inner) {
      diag_.Error(cfg->range.start,
                  std::format("config '{}' delegates instance '{}' to unknown "
                              "config '{}'",
                              cfg->name, rule->inst_path, rule->use_cell));
      continue;
    }
    if (inner->design_cells.empty()) continue;
    std::string outer_path(rule->inst_path);
    const auto& [inner_lib, inner_cell] = inner->design_cells.front();
    instance_use_overrides_.emplace_back(outer_path, std::string(inner_lib),
                                         std::string(inner_cell));

    std::string_view inner_top = inner_cell;
    for (auto* irule : inner->rules) {
      if (irule->kind == ConfigRuleKind::kDefault) {
        if (irule->liblist.empty()) continue;
        std::vector<std::string> libs;
        libs.reserve(irule->liblist.size());
        for (auto lib : irule->liblist) libs.emplace_back(lib);
        instance_liblist_overrides_.emplace_back(outer_path, std::move(libs));
      } else if (irule->kind == ConfigRuleKind::kInstance) {
        if (irule->liblist.empty()) continue;
        std::string_view ipath = irule->inst_path;
        bool path_matches =
            ipath == inner_top ||
            (ipath.size() > inner_top.size() && ipath.starts_with(inner_top) &&
             ipath[inner_top.size()] == '.');
        if (!path_matches) continue;
        std::string translated = outer_path;
        if (ipath.size() > inner_top.size()) {
          translated.append(ipath.substr(inner_top.size()));
        }
        std::vector<std::string> libs;
        libs.reserve(irule->liblist.size());
        for (auto lib : irule->liblist) libs.emplace_back(lib);
        instance_liblist_overrides_.emplace_back(std::move(translated),
                                                 std::move(libs));
      }
    }
  }

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
