#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/dollar_parameter_values.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/nettype_registration.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_ref_walks.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

size_t LibrarySearchPosition(std::string_view library,
                             const std::vector<std::string>& order) {
  for (size_t i = 0; i < order.size(); ++i) {
    if (order[i] == library) return i;
  }
  return order.size();
}

bool SelectedLibraryListInForce(const std::vector<std::string>& order,
                                bool strict) {
  return strict && !order.empty();
}

bool LibraryExcludedBySelectedList(std::string_view library,
                                   const std::vector<std::string>& order,
                                   bool strict) {
  if (!SelectedLibraryListInForce(order, strict)) return false;
  return LibrarySearchPosition(library, order) == order.size();
}

namespace {

ModuleDecl* FindCellInLibrary(std::string_view target_lib,
                              std::string_view use_cell,
                              CompilationUnit* unit) {
  const std::vector<ModuleDecl*>* const kCellKinds[] = {
      &unit->modules, &unit->interfaces, &unit->programs, &unit->checkers};
  for (const auto* decls : kCellKinds) {
    for (auto* decl : *decls) {
      if (decl->is_extern) continue;
      if (decl->library == target_lib && decl->name == use_cell) return decl;
    }
  }
  return nullptr;
}

std::optional<ModuleDecl*> FindInstanceUseOverride(
    const std::string& current_inst_path,
    const std::vector<std::tuple<std::string, std::string, std::string>>&
        instance_use_overrides,
    CompilationUnit* unit) {
  if (current_inst_path.empty()) return std::nullopt;
  for (const auto& [path, ulib, ucell] : instance_use_overrides) {
    if (path != current_inst_path) continue;
    return FindCellInLibrary(ulib, ucell, unit);
  }
  return std::nullopt;
}

template <typename Decls>
static void AppendNamedDecls(const Decls& decls, std::string_view name,
                             std::vector<ModuleDecl*>& candidates) {
  for (auto* d : decls) {
    if (d->name == name && !d->is_extern) candidates.push_back(d);
  }
}

void CollectModuleCandidates(std::string_view name, CompilationUnit* unit,
                             std::vector<ModuleDecl*>& candidates,
                             ModuleDecl*& extern_decl) {
  for (auto* mod : unit->modules) {
    if (mod->name != name) continue;
    if (mod->is_extern) {
      if (!extern_decl) extern_decl = mod;
    } else {
      candidates.push_back(mod);
    }
  }
  AppendNamedDecls(unit->interfaces, name, candidates);
  AppendNamedDecls(unit->programs, name, candidates);
  AppendNamedDecls(unit->checkers, name, candidates);
}

std::vector<ModuleDecl*> FilterCandidatesByLibrary(
    const std::vector<ModuleDecl*>& candidates,
    const std::vector<std::string>& liblist) {
  std::vector<ModuleDecl*> filtered;
  filtered.reserve(candidates.size());
  for (auto* c : candidates) {
    for (const auto& lib : liblist) {
      if (lib == c->library) {
        filtered.push_back(c);
        break;
      }
    }
  }
  return filtered;
}

ModuleDecl* PickByLibraryOrder(const std::vector<ModuleDecl*>& candidates,
                               const std::vector<std::string>& order) {
  ModuleDecl* best = candidates.front();
  size_t best_pri = LibrarySearchPosition(best->library, order);
  for (size_t i = 1; i < candidates.size(); ++i) {
    size_t pri = LibrarySearchPosition(candidates[i]->library, order);
    if (pri < best_pri) {
      best = candidates[i];
      best_pri = pri;
    }
  }
  return best;
}

ModuleDecl* FindNonModuleDesign(std::string_view name, CompilationUnit* unit) {
  auto pit = std::find_if(
      unit->programs.begin(), unit->programs.end(),
      [name](auto* p) { return p->name == name && !p->is_extern; });
  if (pit != unit->programs.end()) return *pit;

  auto iit = std::find_if(
      unit->interfaces.begin(), unit->interfaces.end(),
      [name](auto* i) { return i->name == name && !i->is_extern; });
  if (iit != unit->interfaces.end()) return *iit;

  auto cit = std::find_if(unit->checkers.begin(), unit->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit->checkers.end()) return *cit;

  return nullptr;
}

void RecordPackageConstant(std::string_view pkg_name, std::string_view name,
                           int64_t value, ScopeMap& cu_param_scope,
                           Arena& arena) {
  auto* qname = arena.Create<std::string>(std::string(pkg_name) + "." +
                                          std::string(name));
  cu_param_scope[*qname] = value;
}

struct PackageRegistration {
  const PackageDecl& pkg;
  ScopeMap values;
  ScopeMap& cu_param_scope;
  Arena& arena;
};

void RegisterOnePackageParam(ModuleItem* item, PackageRegistration& reg) {
  if (item->kind != ModuleItemKind::kParamDecl || !item->init_expr) return;
  const DataType kType = InPackageScope(item->data_type, reg.pkg);
  auto val = FoldDeclaredParamValue(item->init_expr, kType, reg.values);
  if (!val) return;
  RecordPackageConstant(reg.pkg.name, item->name, *val, reg.cu_param_scope,
                        reg.arena);
  reg.values[item->name] = *val;
  auto reading = TwoStateReading(item->init_expr, kType, reg.values, *val);
  SetTwoStateReading(reg.values, item->name, reading);
  SetTwoStateReading(reg.cu_param_scope,
                     std::string(reg.pkg.name) + "." + std::string(item->name),
                     reading);
}

void RegisterPackageParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                           Arena& arena) {
  for (auto* pkg : unit->packages) {
    PackageRegistration reg{*pkg, cu_param_scope, cu_param_scope, arena};
    for (auto* item : pkg->items) {
      BindPackageImportConstants(pkg, item, cu_param_scope, reg.values);
      for (const auto& m : BindEnumConstantsOfItem(item, reg.values, arena))
        RecordPackageConstant(pkg->name, m.name, m.value, cu_param_scope,
                              arena);
      RegisterOnePackageParam(item, reg);
    }
  }
}

std::string_view RegisterScopedTypedef(std::string_view scope_name,
                                       std::string_view type_name,
                                       const DataType& dtype,
                                       TypedefMap& typedefs, Arena& arena) {
  auto* qname = arena.Create<std::string>(std::string(scope_name) +
                                          "::" + std::string(type_name));
  typedefs[*qname] = dtype;
  return *qname;
}

void RegisterPackageTypedefs(
    CompilationUnit* unit, TypedefMap& typedefs,
    std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims,
    Arena& arena) {
  for (auto* pkg : unit->packages) {
    for (auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kTypedef) continue;
      std::string_view key = RegisterScopedTypedef(
          pkg->name, item->name, PackageTypedefType(*item, *pkg, arena),
          typedefs, arena);
      if (!item->unpacked_dims.empty())
        td_array_dims[key] = item->unpacked_dims;
    }
  }
}

static void MarkPackageStagedArrays(CompilationUnit* unit) {
  for (auto* pkg : unit->packages) {
    std::unordered_set<std::string_view> array_typedefs;
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kTypedef &&
          !item->unpacked_dims.empty())
        array_typedefs.insert(item->name);
    }
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kVarDecl &&
          item->data_type.kind == DataTypeKind::kNamed &&
          !item->unpacked_dims.empty() &&
          array_typedefs.contains(item->data_type.type_name)) {
        item->data_type.names_unpacked_array = true;
      }
    }
  }
}

void RegisterClassTypedefs(
    CompilationUnit* unit, TypedefMap& typedefs,
    std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims,
    Arena& arena) {
  const ClassTypedefTables kTables{unit, typedefs, td_array_dims, arena};
  for (auto* cls : unit->classes) {
    RegisterClassTypedefKeys(cls, cls->name, kTables);
  }
}

void RegisterBuiltinClassNames(
    std::unordered_set<std::string_view>& class_names) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.kind == StdPackageMemberKind::kClass) {
      class_names.insert(entry.name);
    }
  }
}

struct CuScope {
  std::unordered_set<std::string_view>& names;
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& aggregate_typedefs;
  std::unordered_set<std::string_view>& class_names;
  std::unordered_set<std::string_view>& parameterized_classes;
  ScopeMap& param_scope;
  DiagEngine& diag;
  Arena& arena;
};

void ClassifyCuScopeItem(ModuleItem* item, CuScope& scope) {
  if (!item->name.empty()) scope.names.insert(item->name);
  BindEnumConstantsOfItem(item, scope.param_scope, scope.arena);
  if (item->kind == ModuleItemKind::kTypedef) {
    scope.typedefs[item->name] = item->typedef_type;
    if (!item->unpacked_dims.empty())
      scope.aggregate_typedefs.insert(item->name);
  } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    scope.class_names.insert(item->class_decl->name);
    if (!item->class_decl->params.empty())
      scope.parameterized_classes.insert(item->class_decl->name);
  } else if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
    if (!IsConstantExpr(item->init_expr, scope.param_scope)) {
      scope.diag.Error(item->loc,
                       std::format("localparam '{}' initializer is not a "
                                   "constant expression",
                                   item->name),
                       Subclause("6.20.4"));
    }
    auto val = FoldDeclaredParamValue(item->init_expr, item->data_type,
                                      scope.param_scope);
    if (val) {
      scope.param_scope[item->name] = *val;
      SetTwoStateReading(scope.param_scope, item->name,
                         TwoStateReading(item->init_expr, item->data_type,
                                         scope.param_scope, *val));
    }
  }
}

static void RegisterUnitScopedType(
    const ModuleItem& item, TypedefMap& typedefs,
    std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims,
    const NettypeTables& nettypes, Arena& arena) {
  if (item.kind == ModuleItemKind::kTypedef) {
    std::string_view key = RegisterScopedTypedef(
        "$unit", item.name, item.typedef_type, typedefs, arena);
    if (!item.unpacked_dims.empty()) td_array_dims[key] = item.unpacked_dims;
  } else if (item.kind == ModuleItemKind::kNettypeDecl) {
    CopyNettype(item.name,
                *arena.Create<std::string>("$unit::" + std::string(item.name)),
                typedefs, nettypes);
  }
}

static void RegisterScopedClassNames(
    const CompilationUnit* unit,
    std::unordered_set<std::string_view>& class_names, Arena& arena) {
  auto record = [&](std::string_view scope, std::string_view name) {
    class_names.insert(*arena.Create<std::string>(std::string(scope) +
                                                  "::" + std::string(name)));
  };
  for (const auto* pkg : unit->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl)
        record(pkg->name, item->class_decl->name);
    }
  }
  for (const auto* cls : unit->classes) record("$unit", cls->name);
}

void RegisterCuClasses(
    CompilationUnit* unit, std::unordered_set<std::string_view>& class_names,
    std::unordered_set<std::string_view>& cu_scope_names,
    std::unordered_set<std::string_view>& parameterized_classes) {
  for (auto* cls : unit->classes) {
    class_names.insert(cls->name);
    cu_scope_names.insert(cls->name);
    if (!cls->params.empty()) parameterized_classes.insert(cls->name);
  }
}

void RegisterAnonymousProgramNames(
    CompilationUnit* unit, std::unordered_set<std::string_view>& names) {
  for (const auto* item : unit->cu_items) {
    if (item->from_anonymous_program) names.insert(item->name);
  }
  for (const auto* pkg : unit->packages) {
    for (const auto* item : pkg->items) {
      if (item->from_anonymous_program) names.insert(item->name);
    }
  }
  names.erase(std::string_view{});
}

}  // namespace

static TypedefScopes InheritedTypedefScopes(const ClassDecl* cls,
                                            const CompilationUnit* unit) {
  std::vector<const ClassDecl*> bases;
  for (const ClassDecl* base = FindBaseClass(cls, unit); base != nullptr;
       base = FindBaseClass(base, unit)) {
    bases.push_back(base);
  }
  TypedefScopes scopes;
  for (auto base = bases.rbegin(); base != bases.rend(); ++base) {
    for (const auto* m : (*base)->members) {
      if (m->kind == ClassMemberKind::kTypedef)
        EnterTypedefScope(scopes, *m->typedef_item, (*base)->name);
    }
  }
  return scopes;
}

void RegisterClassTypedefKeys(const ClassDecl* cls, std::string_view scope,
                              const ClassTypedefTables& tables) {
  TypedefScopes scopes = InheritedTypedefScopes(cls, tables.unit);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr) {
      std::string_view key = RegisterScopedTypedef(
          scope, m->name,
          InTypedefScopes(m->typedef_item->typedef_type, scopes, tables.arena),
          tables.typedefs, tables.arena);
      EnterTypedefScope(scopes, *m->typedef_item, scope);
      if (!m->typedef_item->unpacked_dims.empty())
        tables.td_array_dims[key] = m->typedef_item->unpacked_dims;
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      auto* nested = tables.arena.Create<std::string>(
          std::string(scope) + "::" + std::string(m->nested_class->name));
      RegisterClassTypedefKeys(m->nested_class, *nested, tables);
    }
  }
}

UdpDecl* FindUdpInLibrary(std::string_view library, std::string_view cell,
                          CompilationUnit* unit) {
  UdpDecl* prototype = nullptr;
  for (auto* udp : unit->udps) {
    if (udp->library != library || udp->name != cell) continue;
    if (!udp->is_extern) return udp;
    prototype = udp;
  }
  return prototype;
}

bool CellUseOverrideApplies(std::string_view src_lib, std::string_view name,
                            CompilationUnit* unit) {
  if (src_lib.empty()) return true;
  return FindCellInLibrary(src_lib, name, unit) != nullptr ||
         FindUdpInLibrary(src_lib, name, unit) != nullptr;
}

void Elaborator::RegisterCuScopeItems() {
  RegisterBuiltinClassNames(class_names_);
  TypedefRegistryGuard typedef_guard(&typedefs_, &aggregate_typedef_names_,
                                     &type_ref_compare_);
  CuScope cu_scope{cu_scope_names_,
                   typedefs_,
                   aggregate_typedef_names_,
                   class_names_,
                   parameterized_class_names_,
                   cu_param_scope_,
                   diag_,
                   arena_};
  ResolveUnitScopeTypeRefs(unit_, arena_, unit_scope_type_refs_);
  RegisterPackageTypedefs(unit_, typedefs_, td_array_dims_, arena_);
  RegisterPackageNettypes(
      unit_, typedefs_,
      {nettype_names_, nettype_resolve_funcs_, nettype_canonical_}, arena_);
  RegisterScopedClassNames(unit_, class_names_, arena_);
  MarkPackageStagedArrays(unit_);
  RegisterPackageParams(unit_, cu_param_scope_, arena_);
  for (auto* item : unit_->cu_items) {
    ClassifyCuScopeItem(item, cu_scope);
    if (item->kind == ModuleItemKind::kTypedef && !item->unpacked_dims.empty())
      td_array_dims_[item->name] = item->unpacked_dims;
    if (item->kind == ModuleItemKind::kNettypeDecl) {
      typedefs_[item->name] = item->typedef_type;
      nettype_names_.insert(item->name);
      RegisterNettypeResolutionAndCanonical(item);
    }
    RegisterUnitScopedType(
        *item, typedefs_, td_array_dims_,
        {nettype_names_, nettype_resolve_funcs_, nettype_canonical_}, arena_);
  }
  RegisterCuClasses(unit_, class_names_, cu_scope_names_,
                    parameterized_class_names_);
  RegisterAnonymousProgramNames(unit_, anonymous_program_names_);
  RegisterClassTypedefs(unit_, typedefs_, td_array_dims_, arena_);
  RegisterClassParams(unit_, cu_param_scope_, arena_, diag_);
  CheckClassParamDollarValues(unit_, {typedefs_, td_array_dims_, class_names_},
                              diag_);
  CheckUnitDollarOperands(*unit_, diag_);
  ResolveUnitScopeFormalTypes(unit_, typedefs_, arena_);
  all_typedefs_ = typedefs_;
  all_cu_param_scope_ = cu_param_scope_;
  all_td_array_dims_ = td_array_dims_;
}

static bool CellClauseSelects(std::string_view src_lib,
                              const ModuleDecl* found) {
  return src_lib.empty() || (found != nullptr && found->library == src_lib);
}

std::optional<ModuleDecl*> Elaborator::ResolveCellUseOverride(
    std::string_view name, const ModuleDecl* found) const {
  auto it = cell_clause_use_overrides_.find(std::string(name));
  if (it == cell_clause_use_overrides_.end()) return std::nullopt;
  const auto& ov = it->second;

  if (!CellClauseSelects(ov.src_lib, found)) return std::nullopt;

  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindCellInLibrary(target_lib, ov.use_cell, unit_);
}

std::optional<ModuleDecl*> Elaborator::ResolveInstanceBindOverride() const {
  if (config_inst_path_.empty()) return std::nullopt;
  for (const auto& [path, ulib, ucell] : instance_bind_overrides_) {
    if (path != config_inst_path_) continue;
    std::string_view target_lib = ulib.empty()
                                      ? std::string_view(current_library_)
                                      : std::string_view(ulib);
    return FindCellInLibrary(target_lib, ucell, unit_);
  }
  return std::nullopt;
}

namespace {

std::string JoinLibraries(const std::vector<std::string>& libs) {
  std::string joined;
  for (const auto& lib : libs) {
    if (!joined.empty()) joined += ' ';
    joined += lib;
  }
  return joined;
}

}  // namespace

std::optional<std::pair<std::string, std::string>>
ElaboratorData::UseTargetInForce(CompilationUnit* unit, const std::string& path,
                                 std::string_view name) const {
  for (const auto& [rule_path, lib, cell] : instance_use_overrides_) {
    if (rule_path == path) return std::make_pair(lib, cell);
  }
  for (const auto& [rule_path, lib, cell] : instance_bind_overrides_) {
    if (rule_path != path) continue;
    return std::make_pair(lib.empty() ? current_library_ : lib, cell);
  }
  auto it = cell_clause_use_overrides_.find(std::string(name));
  if (it != cell_clause_use_overrides_.end() &&
      CellUseOverrideApplies(it->second.src_lib, name, unit)) {
    const auto& ov = it->second;
    return std::make_pair(ov.use_lib.empty() ? current_library_ : ov.use_lib,
                          ov.use_cell);
  }
  return std::nullopt;
}

static std::pair<const std::vector<std::string>*, size_t> NearestLiblistRule(
    const std::string& inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        overrides) {
  if (inst_path.empty()) return {nullptr, 0};
  const std::vector<std::string>* inherited = nullptr;
  size_t best_match_len = 0;
  for (const auto& [rule_path, libs] : overrides) {
    bool matches = inst_path == rule_path ||
                   (inst_path.size() > rule_path.size() &&
                    inst_path.compare(0, rule_path.size(), rule_path) == 0 &&
                    inst_path[rule_path.size()] == '.');
    if (matches && rule_path.size() >= best_match_len) {
      inherited = &libs;
      best_match_len = rule_path.size();
    }
  }
  return {inherited, best_match_len};
}

static const std::vector<std::string>* OwnInstanceLiblist(
    const std::string& inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        overrides) {
  auto [libs, len] = NearestLiblistRule(inst_path, overrides);
  return len == inst_path.size() ? libs : nullptr;
}

void ElaboratorData::RecordCellClauseListBinding(std::string_view cell) {
  if (!in_config_elaboration_ || config_inst_path_.empty() ||
      OwnInstanceLiblist(config_inst_path_, instance_liblist_overrides_) !=
          nullptr) {
    return;
  }
  auto it = cell_clause_liblist_overrides_.find(std::string(cell));
  if (it == cell_clause_liblist_overrides_.end()) return;
  cell_liblist_bindings_.emplace_back(config_inst_path_, it->second);
}

bool ElaboratorData::ReportConfigRuleBindingNothing(CompilationUnit* unit,
                                                    const ModuleItem* item,
                                                    DiagEngine& diag) const {
  const std::string& path = config_inst_path_;
  std::string_view name = item->inst_module;
  if (auto use = UseTargetInForce(unit, path, name)) {
    diag.Error(item->loc,
               std::format("unknown module '{}': the configuration binds "
                           "instance '{}' to {}.{}, and library '{}' holds "
                           "no cell '{}'",
                           name, path, use->first, use->second, use->first,
                           use->second),
               Subclause("33.4.1.6"));
    return true;
  }
  const std::vector<std::string>* libs = SelectedLiblist(name);
  std::string_view which = "library list";
  if (libs == nullptr &&
      SelectedLibraryListInForce(library_order_, library_order_strict_)) {
    libs = &library_order_;
    which = "default library list";
  }
  const std::vector<std::string> kParentLibrary{current_library_};
  if (in_config_elaboration_ && !current_library_.empty() &&
      (libs == nullptr || libs->empty())) {
    libs = &kParentLibrary;
    which = "parent cell's library";
  }
  if (libs == nullptr) return false;
  diag.Error(
      item->loc,
      std::format("unknown module '{}': the configuration's {} ({}) holds "
                  "no cell '{}' for instance '{}'",
                  name, which, JoinLibraries(*libs), name, path),
      Subclause("33.4.1.5"));
  return true;
}

std::string HierInstancePath(std::string_view parent, const HierPath& gen_steps,
                             std::string_view inst_name) {
  std::string path(parent);
  auto level = [&path](std::string_view name) {
    if (!path.empty()) path.push_back('.');
    path.append(name);
  };
  for (const auto& step : gen_steps) {
    level(step.name);
    if (step.has_index) path += std::format("[{}]", step.index);
  }
  level(inst_name);
  return path;
}

static ModuleDecl* PickCandidateByGlobalOrder(
    std::vector<ModuleDecl*> candidates,
    const std::vector<std::string>& library_order, bool library_order_strict) {
  if (SelectedLibraryListInForce(library_order, library_order_strict) &&
      !candidates.empty()) {
    candidates = FilterCandidatesByLibrary(candidates, library_order);
  }
  if (candidates.empty()) return nullptr;
  return PickByLibraryOrder(candidates, library_order);
}

const std::vector<std::string>* ElaboratorData::SelectedLiblist(
    std::string_view name) const {
  if (const auto* own =
          OwnInstanceLiblist(config_inst_path_, instance_liblist_overrides_)) {
    return own;
  }
  if (auto it = cell_clause_liblist_overrides_.find(std::string(name));
      it != cell_clause_liblist_overrides_.end()) {
    return &it->second;
  }
  auto [inst, inst_len] =
      NearestLiblistRule(config_inst_path_, instance_liblist_overrides_);
  auto [cell, cell_len] =
      NearestLiblistRule(config_inst_path_, cell_liblist_bindings_);
  return cell_len > inst_len ? cell : inst;
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  if (auto hit = FindInstanceUseOverride(config_inst_path_,
                                         instance_use_overrides_, unit_);
      hit.has_value()) {
    return *hit;
  }

  if (auto hit = ResolveInstanceBindOverride(); hit.has_value()) {
    return *hit;
  }

  ModuleDecl* found = SearchModule(name);
  if (auto hit = ResolveCellUseOverride(name, found); hit.has_value()) {
    return *hit;
  }
  return found;
}

ModuleDecl* Elaborator::SearchModule(std::string_view name) const {
  ModuleDecl* extern_decl = nullptr;
  std::vector<ModuleDecl*> candidates;
  CollectModuleCandidates(name, unit_, candidates, extern_decl);

  const std::vector<std::string>* override_liblist = SelectedLiblist(name);
  const std::vector<std::string> kParentLibrary{current_library_};
  if (in_config_elaboration_ && !current_library_.empty() &&
      (override_liblist != nullptr
           ? override_liblist->empty()
           : !SelectedLibraryListInForce(library_order_,
                                         library_order_strict_))) {
    override_liblist = &kParentLibrary;
  }

  bool selected_list_governed =
      SelectedLibraryListInForce(library_order_, library_order_strict_);
  if (override_liblist != nullptr) {
    candidates = FilterCandidatesByLibrary(candidates, *override_liblist);
    if (!candidates.empty()) {
      return PickByLibraryOrder(candidates, *override_liblist);
    }
    return extern_decl;
  }
  if (ModuleDecl* picked = PickCandidateByGlobalOrder(
          std::move(candidates), library_order_, library_order_strict_)) {
    return picked;
  }
  if (extern_decl) return extern_decl;
  if (selected_list_governed) return nullptr;

  return FindNonModuleDesign(name, unit_);
}

ModuleDecl* Elaborator::FindDesignCell(std::string_view library,
                                       std::string_view cell) const {
  if (library.empty()) return FindModule(cell);
  return FindCellInLibrary(library, cell, unit_);
}

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  auto outer = enclosing_nested_decls_.find(name);
  if (outer != enclosing_nested_decls_.end()) return outer->second;
  return FindModule(name);
}

}  // namespace delta
