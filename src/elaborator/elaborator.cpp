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
#include "elaborator/elaborator_child_type_params.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_node_attributes.h"
#include "elaborator/elaborator_type_facts.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/package_assertion_scope.h"
#include "elaborator/rtlir.h"
#include "elaborator/sdf_annotate_calls.h"
#include "elaborator/time_literal_scale.h"
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
// §23.11 (printed page 771): a bind_instantiation amounts to a complete module,
// interface, program or checker instantiation statement, so the module a bind
// directive names appears in an instantiation and is no top-level module
// (§23.3.1); run as a top as well, a module bound into another ran once more
// with none of its ports connected.
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
  // §3.11 with A.1.6: an interface's items reach module_common_item, so an
  // interface may instantiate a program, which is then no top.
  for (const auto* iface : unit->interfaces) {
    CollectInstantiatedNames(iface->items, instantiated);
    CollectBoundNames(iface->bind_directives, instantiated);
  }
  CollectBoundNames(unit->bind_directives, instantiated);

  std::vector<ModuleDecl*> tops;
  for (auto* mod : unit->modules)
    if (!instantiated.contains(mod->name)) tops.push_back(mod);
  // An extern program header (Syntax 24-1) is a prototype and no program.
  for (auto* prog : unit->programs)
    if (!prog->is_extern && !instantiated.contains(prog->name))
      tops.push_back(prog);
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

// §33.7: the library.cell naming `cfg`, held in `arena` for the modules that
// record it.
std::string_view ConfigLibCell(const ConfigDecl* cfg, Arena& arena) {
  const std::string kName =
      std::string(cfg->library) + "." + std::string(cfg->name);
  return {arena.AllocString(kName.c_str(), kName.size()), kName.size()};
}

// §33.4.2: an instance clause of a configuration reached by delegation names
// its instance from that configuration's own design cell, `inner_top`, down,
// and the instance it stands for is the one at `outer_path` and below it.
// Rewrites `path` that way, answering false for a path the design cell does not
// start, which names no instance of the delegated subtree.
bool RebaseConfigPath(std::string& path, std::string_view inner_top,
                      std::string_view outer_path) {
  const bool kUnder = path == inner_top || (path.size() > inner_top.size() &&
                                            path.starts_with(inner_top) &&
                                            path[inner_top.size()] == '.');
  if (!kUnder) return false;
  path = std::string(outer_path) + path.substr(inner_top.size());
  return true;
}

// Rebases the path every entry of `table` carries, as `path_of` reads it, and
// drops the entries no instance of the delegated subtree answers to.
template <typename Table, typename PathOf>
void RebaseConfigTable(Table& table, std::string_view inner_top,
                       std::string_view outer_path, PathOf path_of) {
  std::erase_if(table, [&](auto& entry) {
    return !RebaseConfigPath(path_of(entry), inner_top, outer_path);
  });
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
//
// §6.20.2: a localparam declared with a type or a range holds its value
// converted to that type, as any parameter does.
void EvalConfigLocalparams(const ConfigDecl* cfg, ScopeMap& scope) {
  for (const ConfigLocalparam& lp : cfg->local_params) {
    if (lp.is_type || lp.init_expr == nullptr) continue;
    auto val = FoldDeclaredParamValue(lp.init_expr, lp.data_type, scope);
    if (val) scope[lp.name] = *val;
  }
}

// Whether a config localparam was declared with neither a type nor a range, so
// that its literal is its value exactly as written.
bool HoldsItsLiteralAsWritten(const ConfigLocalparam& lp) {
  return !lp.is_type && lp.init_expr != nullptr &&
         IsLiteralKind(lp.init_expr->kind) &&
         lp.data_type.kind == DataTypeKind::kImplicit &&
         lp.data_type.packed_dim_left == nullptr;
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
    // §33.4.1.5: a liblist clause listing no library still selects a list,
    // the empty one, which FindModule reads as the parent cell's library; a
    // use clause selects none.
    const bool kUseExpansion = !rule->use_cell.empty() ||
                               !rule->use_lib.empty() || rule->use_config ||
                               RuleCarriesParamOverride(rule);
    if (kUseExpansion) continue;
    overrides.emplace_back(std::string(rule->inst_path),
                           LiblistToStrings(rule->liblist));
  }
}

// Expands instance clauses that delegate to another configuration (§33.4.2)
// into the binding of the instance to that configuration's design cell, and
// records the delegation, below which the configuration's own rules govern. A
// clause delegates when its use clause names a config, which §33.2.1 decides:
// the ':config' extension names one outright, and a name that reaches no other
// design element names the config of that name on its own.
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
  design->cu_timescale = CompilationUnitTimescale(*unit);
  // §3.14.3 counts the smallest precision of every `timescale directive, so
  // pass the finest the preprocessor read rather than the last directive's: a
  // finer directive earlier in the unit is a candidate too, and without any a
  // design whose only timescale comes from a directive resolves to the ns
  // default.
  design->global_time_precision = ComputeGlobalTimePrecision(
      unit, unit->has_preproc_global_precision, unit->preproc_global_precision);
  design->global_precision_order = GlobalTimePrecisionOrder(unit);
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

  ValidatePackageReferences();

  ValidatePackageExports();

  ValidateModports();

  ValidateSpecifyBlocks();

  ReportViewportsContainingNothing(*unit_, diag_);

  RegisterCuScopeItems();

  // After RegisterCuScopeItems above, which is what fills
  // anonymous_program_names_ with the names §24.6's note bars a reference to.
  ValidateProgramWideSpaceAccessInPackageAndCuScopes();

  ValidateCuTypedefs();

  ApplyClassMethodAutomaticDefault();

  DefaultPackageTaskFuncLifetimes();

  // Before any module's registry takes the packages' sequences and
  // properties, so that each instantiates its package's own by the name the
  // package scope gives it.
  ResolvePackageAssertionNames(unit_, arena_);

  ValidatePackageCycleDelays(unit_, diag_);

  // After RegisterCuScopeItems above, which is what fills cu_param_scope_ with
  // the compilation-unit and package parameters the check folds against.
  ValidatePackageValueParams();

  RunPreElaborationClassValidations();

  ValidatePerDeclarationRulesInUnitScopes();

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
    // §33.4.3 Example 3: `instance top use #(.WIDTH(32))` names the design's
    // top-level cell alone, and its assignments are that cell's parameters,
    // so they are applied to the top as a configuration's overrides are to any
    // instance (§33.4.1.3 has an instance name start at the top-level module).
    ParamList top_params;
    std::vector<std::string_view> config_locked;
    ModuleItem top_item;
    top_item.inst_module = mod_decl->name;
    // §3.12.1: a top-level module stands in its compilation unit, whose
    // parameters are the names an override of it reads.
    ApplyConfigParamOverrides(&top_item, mod_decl, top_params, cu_param_scope_,
                              config_locked);
    // §6.20.3: no instantiation assigns a top-level module's type parameters,
    // so each takes its default, or a configuration's assignment, and is
    // published as ElaborateModuleInst publishes a child's, for `$bits(T)` and
    // a declaration of type T to read. A type parameter with no default is
    // reported among the top's parameters, and none is published then.
    AppliedTypeParams applied_type_params;
    if (AllTypeParamsHaveDefaults(mod_decl)) {
      applied_type_params = ApplyChildTypeParams(
          TypeParamSourcesFor(&top_item, instance_param_overrides_,
                              config_inst_path_),
          mod_decl, typedefs_, unit_, diag_);
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
  // Every pass from here on runs outside any module. ApplyDefparamsRecursively
  // resolves a defparam whose hierarchical path crosses modules, and
  // FinalizeDesignTail computes a width for every typedef in the design, so
  // both read the union of what the modules registered rather than the scope
  // the last one happened to leave behind. ProcessPendingGenerate does not:
  // §26.3 makes an imported name locally visible only before that point in the
  // current scope, so it installs the maps Elaborator::ElaborateBehavioralItem
  // captured onto each PendingGenerate (elaborator/pending_generate.h) instead
  // of reading these three.
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
  // §32.4.4: what an SDF interconnect entry names is found by walking the
  // parsed hierarchy, so the design keeps the way back to it. See
  // RtlirDesign::compilation_unit.
  design->compilation_unit = unit_;
  design->compilation_units = units_.units;
  design->top_decls.assign(top_decls.begin(), top_decls.end());
  top_decls_ = design->top_decls;
  ResetPendingElaboration();
  // §13.4.3 with §20.10.1: a folded constant function's severity tasks.
  ConstFuncSeverityGuard severity_guard(diag_, arena_);

  if (!ElaborateTopModules(top_decls, design)) return nullptr;

  // §23.8: every top-level module is a root a defparam's name may start over
  // from, and the tops are all elaborated now.
  defparam_top_roots_ = design->top_modules;
  ResolveDefparamsAndGenerates(design);

  for (auto* top : design->top_modules) WarnUnresolvedDefparams(top);
  // §23.11: a bind directive's target is read against the whole design, so
  // every top is walked before a target that matched nothing is reported.
  ApplyBindDirectives(design->top_modules);
  // §23.11 elaborates a bound instance as though it were written in its
  // target, and ApplyBindInstance does so through ElaborateModule, which queues
  // the bound module's generate constructs as any module's are. The queue was
  // drained above, before any bind was applied, so what the bound modules
  // queued is drained here, each batch in turn as a block's own generates
  // queue more (§27.3, §27.5).
  while (!pending_generates_.empty()) {
    std::vector<PendingGenerate> batch;
    batch.swap(pending_generates_);
    for (const auto& pg : batch) ProcessPendingGenerate(pg);
  }

  for (auto* top : design->top_modules) {
    ValidateModportExportConflicts(top);

    CollectAllModules(top, design->all_modules);
  }
  // §23.3.3.6: whether the design calls $sdf_annotate is known only now.
  WarnUwireNetsKeptApart(*design, diag_);
  // §23.3.3.7.1: every interconnect port connection is known only now.
  interconnect_merges_.Resolve(diag_);

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
  // §37.83: the attributes of the classes and package properties outside
  // every module, which the tail has just put on the design.
  RecordDesignAttributes(*design, diag_, cu_param_scope_);
  UnitScopeTables::PopulateUnitTypeFacts(*this, design);
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
    UnitScopeTables::RunPreElaborationValidations(*this);
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
    // §33.5.4: a top-level cell may be named lib.cell, which takes it from
    // that library alone.
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

// §33.4.3: record the parameter overrides each instance clause carries so they
// can be applied as the matching instance is elaborated.
// §33.4.3 (printed page 940): a localparam declared in a configuration has to
// be given a value, and only a literal one, so an override naming one carries
// that literal itself, as wide as it was written -- a string of any length
// rather than the 64 bits the folded localparam holds.
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

// One cell clause's use expansion, binding every instance of its cell. §33.4.2:
// one binding the cell to a configuration hands each of those instances to that
// configuration's rules as well.
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
      CollectCellUseOverride(cfg, rule);
      continue;
    }
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        LiblistToStrings(rule->liblist);
  }
}

// §33.4.1.6: an instance clause whose use expansion names a cell binds that
// specific instance to the exact library.cell named. A use clause that names a
// config instead is expanded by CollectConfigDelegationOverrides and so is
// skipped here; §33.2.1 settles which of the two a given name is.
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
  // §33.4.2: the configuration's rules name their instances from its own
  // design cell down, which here is the delegated instance.
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

// The rule tables one configuration fills that say which cell an instance
// binds to: the default list, the cell clauses, the instance clauses' lists
// and uses, and the delegations to other configurations.
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
