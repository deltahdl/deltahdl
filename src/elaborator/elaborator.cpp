#include "elaborator/elaborator.h"

#include <algorithm>
#include <cstddef>
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
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_type_facts.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
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

// §23.3.1: record the name of every module instantiated by `item`, descending
// through generate constructs (whose alternatives live in gen_body / gen_else /
// gen_case_items) and nested module declarations. Non-instantiating items carry
// empty gen_* fields, so the recursion is a no-op for them.
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

// §23.3.1: the top-level modules of a compilation unit are the modules present
// in the source but not instantiated by any other module, and §24.3 has a
// top-level program that is not explicitly instantiated implicitly
// instantiated once, under its declaration name. Returns the modules in source
// order and the programs after them; used when no explicit top module is
// named.
//
// An interface or checker nothing instantiates is elaborated by no run and so
// validated by none: §23.3.1 and §24.3 say that of modules and programs alone,
// and an interface reaches Elaborator::ElaborateModule only through
// Elaborator::FindModule, whose CollectModuleCandidates appends
// unit->interfaces, unit->programs and unit->checkers. A design element that is
// never instantiated contributes nothing to the elaborated design, so the
// asymmetry is deliberate rather than an omission here.
// §23.11 (printed page 771): "The bind_instantiation is effectively a complete
// module, interface, program, or checker instantiation statement", so the
// module a bind directive names appears in an instantiation and is no
// top-level module (§23.3.1); run as a top as well, a module bound into
// another ran once more with none of its ports connected.
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
  for (const auto* iface : unit->interfaces)
    CollectBoundNames(iface->bind_directives, instantiated);
  CollectBoundNames(unit->bind_directives, instantiated);

  std::vector<ModuleDecl*> tops;
  for (auto* mod : unit->modules)
    if (!instantiated.contains(mod->name)) tops.push_back(mod);
  for (auto* prog : unit->programs)
    if (!instantiated.contains(prog->name)) tops.push_back(prog);
  return tops;
}

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
  // A config that shares its name with a module or a primitive is reached only
  // through the explicit extension, because the plain name reaches the cell
  // (§33.2.1). Where the name belongs to no cell, nothing else can be meant.
  if (NonConfigCellNames(unit).contains(rule->use_cell)) return false;
  return FindDelegatedConfig(unit->configs, cfg, rule->use_cell) != nullptr;
}

namespace {

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

// Expands instance clauses that delegate to another configuration (§33.4.1)
// into instance use overrides plus translated liblist overrides. A clause
// delegates when its use clause names a config, which §33.2.1 decides: the
// ':config' extension names one outright, and a name that reaches no other
// design element names the config of that name on its own.
void CollectConfigDelegationOverrides(
    const ConfigDecl* cfg, const CompilationUnit* unit, DiagEngine& diag,
    std::vector<std::tuple<std::string, std::string, std::string>>&
        use_overrides,
    std::vector<std::pair<std::string, std::vector<std::string>>>&
        liblist_overrides) {
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

    std::string_view inner_top = inner_first.cell;
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

  // §20.4.1: carry the compilation unit's timescale (reported by the $unit
  // argument) and the simulation time unit (the smallest precision across the
  // design, reported by $root; see §3.14.3) onto the finished design.
  if (unit->has_cu_timeunit) {
    design->cu_timescale.unit = unit->cu_time_unit;
    design->cu_timescale.magnitude = unit->cu_time_unit_magnitude;
  }
  if (unit->has_cu_timeprecision) {
    design->cu_timescale.precision = unit->cu_time_prec;
    design->cu_timescale.prec_magnitude = unit->cu_time_prec_magnitude;
  }
  // The compilation unit records the timescale the preprocessor read from a
  // `timescale directive, so pass it rather than claiming there was none: its
  // precision is one of the candidates the smallest-precision search must
  // consider, and without it a design whose only timescale comes from that
  // directive resolves to the ns default.
  design->global_time_precision = ComputeGlobalTimePrecision(
      unit, unit->has_preproc_timescale, unit->preproc_timescale.precision);
}

// Performs the order-independent data tail of elaboration: computing each
// typedef's bit width and transferring the CU declarations plus the captured
// severity metadata (§20.10.1) onto the finished design.
void FinalizeDesignTail(RtlirDesign* design, const CompilationUnit* unit,
                        const TypeNameSources& src,
                        const DesignMetadata& meta) {
  TypeNameFacts facts{design->type_widths,  design->type_kinds,
                      design->type_signed,  design->type_layouts,
                      design->type_targets, design->type_ranges,
                      design->type_enums};
  PopulateTypeWidths(src, facts);
  CopyDesignMetadata(design, unit, meta);
}

// Reports a design statement whose cell was not found. A cell the source
// qualified by a library was searched for in that library alone (§33.2.2), so
// the message names the library the search was confined to; a cell searched for
// more widely than one library is reported by name alone.
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

  // After RegisterCuScopeItems above, which is what fills
  // anonymous_program_names_ with the names §24.6's note bars a reference to.
  ValidateProgramWideSpaceAccessInPackageAndCuScopes();

  ValidateCuTypedefs();

  ApplyClassMethodAutomaticDefault();

  DefaultPackageTaskFuncLifetimes();

  ValidatePackageCycleDelays(unit_, diag_);

  // After RegisterCuScopeItems above, which is what fills cu_param_scope_ with
  // the compilation-unit and package parameters the check folds against.
  ValidatePackageValueParams();

  RunPreElaborationClassValidations();

  ValidatePerDeclarationRulesInUnitScopes();

  ValidateTimescaleConsistency();

  ValidateStandaloneTimescaleOrder();

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
    // §33.4.3 Example 3: `instance top use #(.WIDTH(32))` names the design's
    // top-level cell alone, and its assignments are that cell's parameters,
    // so they are applied to the top as a configuration's overrides are to any
    // instance (§33.4.1.3 has an instance name start at the top-level module).
    ParamList top_params;
    std::vector<std::string_view> config_locked;
    ModuleItem top_item;
    top_item.inst_module = mod_decl->name;
    ApplyConfigParamOverrides(&top_item, mod_decl, top_params, ScopeMap{},
                              config_locked);
    auto* top = ElaborateModule(mod_decl, top_params);
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
  // Every pass from here on runs outside any module. ApplyDefparamsRecursively
  // resolves a defparam whose hierarchical path crosses modules, and
  // FinalizeDesignTail computes a width for every typedef in the design, so
  // both read the union of what the modules registered rather than the scope
  // the last one happened to leave behind. ProcessPendingGenerate does not:
  // §26.3 makes an imported name locally visible only "prior to that point
  // within the current scope", so it installs the maps
  // Elaborator::ElaborateBehavioralItem captured onto each
  // ElaboratorData::PendingGenerate instead of reading these two.
  typedefs_ = all_typedefs_;
  cu_param_scope_ = all_cu_param_scope_;
  return true;
}

// Every module of the tree rooted at `mod`, each given its net delays once.
// The walk keys on the module rather than on its name: two instances of one
// module may hold two RtlirModule objects sharing a name, and a set keyed by
// name would give one of them the pass and skip the other.
void Elaborator::ApplyNetDelaysInModuleTree(RtlirModule* mod) {
  if (mod == nullptr || !net_delay_modules_.insert(mod).second) return;
  ApplyNetDeclDelaysToDrivers(arena_, mod);
  for (auto& child : mod->children) {
    ApplyNetDelaysInModuleTree(child.resolved);
  }
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
  // §32.4.4: what an SDF interconnect entry names is found by walking the
  // parsed hierarchy, so the design keeps the way back to it. See
  // RtlirDesign::compilation_unit.
  design->compilation_unit = unit_;
  design->top_decls.assign(top_decls.begin(), top_decls.end());
  pending_generates_.clear();
  applied_defparams_.clear();
  generate_defparams_.clear();
  defparam_top_roots_.clear();
  defparam_writer_blocks_.clear();

  if (!ElaborateTopModules(top_decls, design)) return nullptr;

  // §23.8: every top-level module is a root a defparam's name may start over
  // from, and the tops are all elaborated now.
  defparam_top_roots_ = design->top_modules;
  ResolveDefparamsAndGenerates(design);

  // §27.5 puts the items of a selected generate block into the enclosing
  // module, and ProcessPendingGenerate appends them to RtlirModule::assigns,
  // ::udp_insts and ::nets after ElaborateItems has run over that module. So
  // the net delays are given to their drivers here, where a module's items are
  // complete: run during ElaborateItems, the pass saw neither a driver written
  // in a generate block nor a net declared in one, and `wire #5 w;` was
  // honoured at module level and ignored one `if` away.
  for (auto* top : design->top_modules) {
    ApplyNetDelaysInModuleTree(top);
  }

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

  // §3.12.1: the constants a class declared outside every module may name in
  // a property's packed dimension (see RtlirDesign::unit_constants). Read here
  // rather than while the modules were elaborated, because ElaborateTopModules
  // has put the union of what every module's imports made visible back into
  // cu_param_scope_ by now, and a compilation-unit class is lowered ahead of
  // the modules, with the design as its only scope.
  design->unit_constants = cu_param_scope_;
  FinalizeDesignTail(
      design, unit_,
      TypeNameSources{typedefs_, aggregate_typedef_names_, arena_},
      DesignMetadata{elab_simulation_blocked_, elab_last_severity_,
                     elab_last_severity_msg_, elab_last_severity_scope_,
                     elab_last_severity_loc_});
  return design;
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  // No explicit top module: root every uninstantiated module as a top per
  // §23.3.1, and every uninstantiated program per §24.3. A package-only or
  // class-only compilation unit has nothing to instantiate but its
  // package/class items still need validation, so it proceeds with an empty
  // top set. A genuinely empty unit (e.g. empty or comment-only source) yields
  // no design.
  if (top_module_name.empty()) {
    if (unit_->DeclaresNothing()) return nullptr;
    RunPreElaborationValidations();
    auto tops = CollectAutoTopModules(unit_);
    // §23.3.1: a design shall contain at least one top-level module. If the
    // unit declares modules but every one is instantiated by another (e.g. a
    // mutual instantiation cycle), no module roots the hierarchy and there is
    // nothing to elaborate. A package- or class-only unit legitimately has no
    // modules, so the check is gated on a non-empty module set.
    if (tops.empty() && !unit_->modules.empty()) {
      diag_.Error(SourceLoc::None(), "design contains no top-level module",
                  Subclause("23.3.1"));
      return nullptr;
    }
    return ElaborateTops(tops);
  }

  RunPreElaborationValidations();

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

  RunPreElaborationValidations();

  std::vector<ModuleDecl*> tops;
  tops.reserve(top_names.size());
  std::unordered_set<std::string_view> already_named;
  for (auto name : top_names) {
    if (!already_named.insert(name).second) continue;
    auto* mod_decl = FindModule(name);
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

// §33.4.3: record the parameter overrides each instance clause carries so they
// can be applied as the matching instance is elaborated.
// §33.4.3 (printed page 940): "A localparam declared in a configuration shall
// be assigned a value and shall only be set to a literal value", so an override
// naming one carries that literal itself, as wide as it was written -- a string
// of any length rather than the 64 bits the folded localparam holds.
static std::vector<std::pair<std::string_view, Expr*>>
OverridesWithLocalparamLiterals(
    const ConfigDecl* cfg,
    std::vector<std::pair<std::string_view, Expr*>> params) {
  for (auto& [pname, pexpr] : params) {
    if (pexpr == nullptr || pexpr->kind != ExprKind::kIdentifier) continue;
    for (const auto& [lname, lexpr] : cfg->local_params) {
      if (lname == pexpr->text && lexpr != nullptr &&
          IsLiteralKind(lexpr->kind)) {
        pexpr = lexpr;
        break;
      }
    }
  }
  return params;
}

// Fills the override `ov` with the parameter overrides `rule` of `cfg`
// carries, for the instances `path` names.
static void FillRuleParamOverride(auto& ov, const ConfigDecl* cfg,
                                  const ConfigRule* rule,
                                  std::string_view path) {
  ov.inst_path.assign(path.data(), path.size());
  ov.reset_all = rule->use_param_reset_all;
  ov.loc = rule->loc;
  ov.params = OverridesWithLocalparamLiterals(cfg, rule->use_params);
}

// §33.4.2: the library and cell a cell clause's use expansion binds; for a
// use clause naming a config, what that config's design statement names, a
// design cell written without a library taken from the library holding the
// config (§33.4.1.1). False where that config holds no design cell.
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

// §33.4.1.4/§33.4.1.6: a cell clause either rebinds a cell through a use
// expansion -- a target cell is required, while the target library may be
// omitted and is then inherited from the parent cell, and a qualifying library
// scopes which instances the clause applies to -- or selects the library list
// (§33.4.1.5) to search for the named cell.
void Elaborator::CollectConfigCellClauseOverrides(const ConfigDecl* cfg) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kCell) continue;
    // §33.4.1.4 with Syntax 33-4's second and third use_clause forms: a cell
    // clause's named parameter assignments apply to every instance of the
    // cell, whether or not the clause also names the cell to bind.
    if (RuleCarriesParamOverride(rule)) {
      FillRuleParamOverride(cell_param_overrides_.emplace_back(), cfg, rule,
                            rule->cell_name);
      if (rule->use_cell.empty()) continue;
    }
    if (!rule->use_cell.empty()) {
      std::string use_lib;
      std::string use_cell;
      if (!CellUseTarget(rule, cfg, unit_, use_lib, use_cell)) continue;
      cell_clause_use_overrides_[std::string(rule->cell_name)] = {
          std::string(rule->cell_lib), std::move(use_lib), std::move(use_cell)};
      continue;
    }
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        LiblistToStrings(rule->liblist);
  }
}

// What a binding clause of a config an instance clause delegates to carries
// onto the delegated instance: a cell clause's use of a cell, an instance
// clause's use of a cell for an instance under the config's design cell, or
// nothing.
enum class DelegatedBinding : uint8_t { kNone, kCellUse, kInstanceBind };

static DelegatedBinding DelegatedBindingOf(const ConfigRule* irule,
                                           const ConfigDecl* inner,
                                           const CompilationUnit* unit,
                                           std::string_view inner_top) {
  if (irule->use_cell.empty() || UseClauseNamesConfig(irule, inner, unit)) {
    return DelegatedBinding::kNone;
  }
  if (irule->kind == ConfigRuleKind::kCell) return DelegatedBinding::kCellUse;
  if (irule->kind == ConfigRuleKind::kInstance &&
      InnerPathUnderTop(irule->inst_path, inner_top)) {
    return DelegatedBinding::kInstanceBind;
  }
  return DelegatedBinding::kNone;
}

// §33.4.1.6: an instance clause whose use expansion names a cell binds that
// specific instance to the exact library.cell named. A use clause that names a
// config instead is expanded by CollectConfigDelegationOverrides and so is
// skipped here; §33.2.1 settles which of the two a given name is.
//
// §33.4.2 (printed page 939): an instance bound to a configuration is "replaced
// with the design hierarchy specified by the configuration", and "the rules
// specified in the config shall determine the configuration of all other
// subinstances". A binding clause of that configuration names its instances
// from its own design cell down, so each is rewritten onto the instance the
// outer clause delegated and recorded here as well.
void Elaborator::CollectConfigInstanceBindOverrides(const ConfigDecl* cfg) {
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance || rule->use_cell.empty()) {
      continue;
    }
    if (!UseClauseNamesConfig(rule, cfg, unit_)) {
      instance_bind_overrides_.emplace_back(std::string(rule->inst_path),
                                            std::string(rule->use_lib),
                                            std::string(rule->use_cell));
      continue;
    }
    const ConfigDecl* inner =
        FindDelegatedConfig(unit_->configs, cfg, rule->use_cell);
    if (inner == nullptr || inner->design_cells.empty()) continue;
    std::string_view inner_top = inner->design_cells.front().cell;
    for (auto* irule : inner->rules) {
      switch (DelegatedBindingOf(irule, inner, unit_, inner_top)) {
        case DelegatedBinding::kCellUse:
          delegated_cell_use_overrides_.push_back(
              {std::string(rule->inst_path),
               std::string(irule->cell_name),
               {std::string(irule->cell_lib), std::string(irule->use_lib),
                std::string(irule->use_cell)}});
          break;
        case DelegatedBinding::kInstanceBind:
          instance_bind_overrides_.emplace_back(
              std::string(rule->inst_path) +
                  std::string(irule->inst_path.substr(inner_top.size())),
              std::string(irule->use_lib), std::string(irule->use_cell));
          break;
        case DelegatedBinding::kNone:
          break;
      }
    }
  }
}

RtlirDesign* Elaborator::Elaborate(const ConfigDecl* cfg) {
  in_config_elaboration_ = true;

  // §33.2.2: which design cells the configuration's own text qualified with a
  // library, recorded before the validations below substitute the library of
  // the configuration itself into the cells left unqualified (§33.4.1.1). A
  // library the statement named is where its cell has to be; a library the
  // statement inherited is only where the search for it starts.
  std::vector<bool> qualified_in_source;
  qualified_in_source.reserve(cfg->design_cells.size());
  for (const auto& design_cell : cfg->design_cells) {
    qualified_in_source.push_back(!design_cell.library.empty());
  }

  RunPreElaborationValidations();

  // A config localparam is restricted to a literal value (§33.4.3), so it can
  // be evaluated once here and made available to parameter-override
  // expressions that reference it.
  EvalConfigLocalparams(cfg, config_localparam_scope_);

  CollectConfigInstanceParamOverrides(cfg);

  // §33.4.1.1, §33.4.1.5: the top-level design cell is named by the design
  // statement (its library defaults to the config's library when omitted); the
  // default clause selects instances, not the top cell, so resolve the top cell
  // before the default library list is installed -- otherwise a top whose
  // library is absent from the default liblist would be filtered away and the
  // design would fail to elaborate.
  //
  // §33.2.2: the library qualifying a design cell says where that cell's
  // source description comes from, so a cell the configuration's text
  // qualified is taken from the named library and a like-named cell held by
  // any other library is not a substitute for it.
  std::vector<ModuleDecl*> top_decls;
  top_decls.reserve(cfg->design_cells.size());
  for (size_t i = 0; i < cfg->design_cells.size(); ++i) {
    const ConfigDesignCell& design_cell = cfg->design_cells[i];
    auto* md = FindDesignCell(design_cell.library, design_cell.cell,
                              qualified_in_source[i]);
    if (!md) {
      auto msg =
          DesignCellNotFoundMessage(cfg->name, design_cell.library,
                                    design_cell.cell, qualified_in_source[i]);
      diag_.Error(design_cell.loc, msg, Subclause("33.4.1.1"));
      return nullptr;
    }
    top_decls.push_back(md);
  }

  ApplyConfigDefaultLiblist(cfg, library_order_, library_order_strict_);

  CollectConfigCellClauseOverrides(cfg);

  CollectInstanceLiblistOverrides(cfg, instance_liblist_overrides_);

  CollectConfigDelegationOverrides(cfg, unit_, diag_, instance_use_overrides_,
                                   instance_liblist_overrides_);

  CollectConfigInstanceBindOverrides(cfg);

  return ElaborateTops(top_decls);
}

}  // namespace delta
