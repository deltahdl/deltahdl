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
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
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

// Returns the cell named use_cell that target_lib holds, or nullptr when that
// library holds no such cell. §33.2.1: a cell is a design element written into
// a library under that element's own name, and §3.2 counts a module, an
// interface, a program and a checker each as a design element, so all four
// kinds are searched. An extern module declaration names a cell without
// defining one, so it is not a cell here.
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

// §33.4.1.3, §33.4.2: when the instance currently being elaborated is the one
// an expansion clause selected, the clause settles what that instance binds.
// Returns nullopt when no instance use override applies (so normal resolution
// should continue), or the override result (which may be nullptr if the named
// cell does not exist).
//
// What the instantiation declares is not consulted. §33.4.1.6's note has the
// binding statement create situations where the unbound instance's module name
// and the cell name it is bound to differ, and §33.4.2 makes that the ordinary
// case for a delegation: the design statement of the configuration an instance
// is handed to specifies the actual binding for that instance, whatever name
// the instantiation was written with.
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

// Appends every declaration in `decls` whose name matches `name` to
// `candidates`.
template <typename Decls>
static void AppendNamedDecls(const Decls& decls, std::string_view name,
                             std::vector<ModuleDecl*>& candidates) {
  for (auto* d : decls) {
    if (d->name == name) candidates.push_back(d);
  }
}

// Partitions modules named `name` into the non-extern candidates and the first
// extern declaration encountered.
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

// Returns the candidates whose library appears in `liblist`, preserving order.
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

// Selects the candidate whose library ranks earliest in `order` (libraries not
// listed rank last). On ties the earlier candidate wins. `candidates` must be
// non-empty.
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

// Resolves `name` to a program, interface, or checker (in that order) when no
// module matched, returning nullptr if none exists.
ModuleDecl* FindNonModuleDesign(std::string_view name, CompilationUnit* unit) {
  auto pit = std::find_if(unit->programs.begin(), unit->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit->programs.end()) return *pit;

  auto iit = std::find_if(unit->interfaces.begin(), unit->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit->interfaces.end()) return *iit;

  auto cit = std::find_if(unit->checkers.begin(), unit->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit->checkers.end()) return *cit;

  return nullptr;
}

// Records one constant a package declares in the compilation-unit parameter
// scope under its fully qualified "package.name" key, which is the spelling
// §26.3's package scope resolution operator reads and A.8.4 admits for a
// parameter and an enum identifier alike. The key is arena-allocated because
// ScopeMap keys are string_views.
void RecordPackageConstant(std::string_view pkg_name, std::string_view name,
                           int64_t value, ScopeMap& cu_param_scope,
                           Arena& arena) {
  auto* qname = arena.Create<std::string>(std::string(pkg_name) + "." +
                                          std::string(name));
  cu_param_scope[*qname] = value;
}

// The constants one package has declared so far, as registration walks its
// items: `values` is the compilation-unit scope with the package's own
// parameters and enumeration constants layered over it under their bare names,
// which §6.20.1 lets a later declaration read, and `cu_param_scope` is where
// each is recorded under its qualified key.
struct PackageRegistration {
  std::string_view pkg_name;
  ScopeMap values;
  ScopeMap& cu_param_scope;
  Arena& arena;
};

// Records a single package value parameter, if it is a value parameter with a
// constant-evaluable initializer. The initializer is folded against the
// package's own constants, because §6.19 declares an enumeration's members as
// constants of the scope the enumeration stands in and §6.20.1 lets a
// parameter read an earlier one: `parameter R = (DEEP | SHALLOW);` names two
// members of an enumeration the package declared, and folding it against the
// compilation-unit scope alone left R unrecorded and `pkg::R` unresolved. It
// is folded at the width the declaration fixes (FoldDeclaredParamValue), as
// a module's parameter is, so `parameter logic [11:0] W = '1` records 4095
// and not the 1 the literal is self-determined (§5.7.1, §6.20.2).
void RegisterOnePackageParam(ModuleItem* item, PackageRegistration& reg) {
  if (item->kind != ModuleItemKind::kParamDecl || !item->init_expr) return;
  auto val =
      FoldDeclaredParamValue(item->init_expr, item->data_type, reg.values);
  if (!val) return;
  RecordPackageConstant(reg.pkg_name, item->name, *val, reg.cu_param_scope,
                        reg.arena);
  reg.values[item->name] = *val;
}

// Records each package's value parameters and enumeration constants in the
// compilation-unit parameter scope under their fully qualified "package.name"
// key (§26.3), each folded against what the package declared before it and,
// §26.3 letting a package import another, against what an earlier import of
// the package brings in by bare name: `import base::K; parameter int KK = K;`
// folds KK to base's K, which the packages' order in the unit has already
// recorded, since §26.3 compiles a package ahead of the scopes importing it.
void RegisterPackageParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                           Arena& arena) {
  for (auto* pkg : unit->packages) {
    PackageRegistration reg{pkg->name, cu_param_scope, cu_param_scope, arena};
    for (auto* item : pkg->items) {
      BindPackageImportConstants(pkg, item, cu_param_scope, reg.values);
      for (const auto& m : BindEnumConstantsOfItem(item, reg.values, arena))
        RecordPackageConstant(pkg->name, m.name, m.value, cu_param_scope,
                              arena);
      RegisterOnePackageParam(item, reg);
    }
  }
}

// Records one typedef under the "Scope::name" key ResolveNamed in
// src/elaborator/type_eval.cpp looks a prefixed name up by. The key is
// arena-allocated because TypedefMap keys are string_views, which a local
// string would leave dangling.
void RegisterScopedTypedef(std::string_view scope_name,
                           std::string_view type_name, const DataType& dtype,
                           TypedefMap& typedefs, Arena& arena) {
  auto* qname = arena.Create<std::string>(std::string(scope_name) +
                                          "::" + std::string(type_name));
  typedefs[*qname] = dtype;
}

// Records each package's typedefs under their qualified key. §26.3 references a
// package's declarations through the package name, as its example on printed
// page 808 does in `ComplexPkg::Complex cout = ComplexPkg::mul(a, b);`, and it
// does so whether or not the package was imported. RegisterImportItem in
// src/elaborator/elaborator_module.cpp enters an imported typedef under its
// bare name, which is the separate spelling an import makes legal.
void RegisterPackageTypedefs(CompilationUnit* unit, TypedefMap& typedefs,
                             Arena& arena) {
  for (auto* pkg : unit->packages) {
    for (auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kTypedef) continue;
      RegisterScopedTypedef(pkg->name, item->name, item->typedef_type, typedefs,
                            arena);
    }
  }
}

// Records each class's typedefs under their qualified key. §8.23 states that
// "type declarations nested inside a class scope are public and can be accessed
// outside the class", through the class name. The reach over unit->classes is
// the one RegisterClassParams already has for the same clause's parameters.
void RegisterClassTypedefs(CompilationUnit* unit, TypedefMap& typedefs,
                           Arena& arena) {
  for (auto* cls : unit->classes) {
    RegisterClassTypedefKeys(cls, cls->name, typedefs, arena);
  }
}

// Inserts the built-in class names that always live in the compilation-unit
// scope: the classes of the std package, which §G.1 lists and
// src/elaborator/std_package.h writes down (§6.14, §26.7).
void RegisterBuiltinClassNames(
    std::unordered_set<std::string_view>& class_names) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.kind == StdPackageMemberKind::kClass) {
      class_names.insert(entry.name);
    }
  }
}

// The compilation-unit scope (§26.3, §6.14): the set of elaborator name spaces
// that compilation-unit items populate -- visible names, typedefs, the
// class/parameterized-class name sets, and the constant parameter scope. These
// containers are members of the Elaborator that are filled together while
// classifying each compilation-unit item, so they travel as one entity.
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

// Classifies one compilation-unit item, recording it in the appropriate
// elaborator scope structures (names, typedefs, class/parameterized-class sets,
// or the constant parameter scope).
void ClassifyCuScopeItem(ModuleItem* item, CuScope& scope) {
  if (!item->name.empty()) scope.names.insert(item->name);
  // §6.19: an enumeration declared here, by a typedef or directly as a data
  // declaration's type, declares its members as constants of the
  // compilation-unit scope, which a later parameter declaration may read.
  BindEnumConstantsOfItem(item, scope.param_scope, scope.arena);
  if (item->kind == ModuleItemKind::kTypedef) {
    scope.typedefs[item->name] = item->typedef_type;
    // §6.18: a compilation-unit typedef never runs Elaborator::ElaborateTypedef
    // (see Elaborator::ValidateCuTypedefs), so the dimensions that make its
    // name stand for an aggregate are recorded here instead.
    if (!item->unpacked_dims.empty())
      scope.aggregate_typedefs.insert(item->name);
  } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    scope.class_names.insert(item->class_decl->name);
    if (!item->class_decl->params.empty())
      scope.parameterized_classes.insert(item->class_decl->name);
  } else if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
    // §6.20.4 lets a local parameter be declared in compilation-unit scope, and
    // rules that `parameter` written there means `localparam`, so the
    // initializer must be a constant expression however it was spelled. Report
    // the breach rather than only leaving the name out of the scope: a name
    // with no value makes every later expression reading it non-constant too,
    // and the report those produce stands at a different declaration and names
    // a different parameter.
    //
    // The report asks IsConstantExpr while the scope keeps the fold, because
    // the two answer different questions: an initializer this elaborator
    // cannot fold to an integer is not thereby a non-constant expression, and
    // a real-valued one folds to neither. The fold is at the width the
    // declaration fixes (FoldDeclaredParamValue), as a package's is.
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
    }
  }
}

// Records each compilation-unit class declaration in the class-name and scope
// sets, flagging parameterized classes (§8.25).
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

// §24.6: every name an anonymous program declares, whichever scope the program
// stands in. "Anonymous programs can be used inside packages (see Clause 26) or
// compilation-unit scopes (see 3.12.1) to declare items that are part of the
// program-wide space without declaring a new scope", and that space is one
// space however a declaration entered it, so the two lists fill one set.
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
  // An item the parser left unnamed is dropped here rather than tested for at
  // each insertion, because an empty name in this set matches every reference
  // position that is itself empty -- a declaration written with no type name
  // carries an empty DataType::type_name, and every such declaration would
  // then be read as naming an anonymous program's class.
  names.erase(std::string_view{});
}

}  // namespace

void RegisterClassTypedefKeys(const ClassDecl* cls, std::string_view scope,
                              TypedefMap& typedefs, Arena& arena) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr) {
      RegisterScopedTypedef(scope, m->name, m->typedef_item->typedef_type,
                            typedefs, arena);
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      auto* nested = arena.Create<std::string>(
          std::string(scope) + "::" + std::string(m->nested_class->name));
      RegisterClassTypedefKeys(m->nested_class, *nested, typedefs, arena);
    }
  }
}

UdpDecl* FindUdpInLibrary(std::string_view library, std::string_view cell,
                          CompilationUnit* unit) {
  // The definition, where one follows or precedes an extern prototype of the
  // primitive (Syntax 29-1), else the prototype.
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
  CuScope cu_scope{cu_scope_names_,
                   typedefs_,
                   aggregate_typedef_names_,
                   class_names_,
                   parameterized_class_names_,
                   cu_param_scope_,
                   diag_,
                   arena_};
  for (auto* item : unit_->cu_items) {
    ClassifyCuScopeItem(item, cu_scope);
    // §7.4.4 (printed page 155) with §6.18: a typedef's unpacked dimensions
    // belong to the type it names, so `ie_t x;` in a module under a
    // compilation-unit `typedef bit ie_t[int];` is an associative array. A
    // compilation-unit typedef is registered here and never elaborated, so
    // the record AdoptTypedefArrayDims (elaborator_decls_var.cpp) reads was
    // filled for a module's typedefs alone, and the declaration was a single
    // bit whose `x[5]` was reported as a select of a scalar.
    if (item->kind == ModuleItemKind::kTypedef && !item->unpacked_dims.empty())
      td_array_dims_[item->name] = item->unpacked_dims;
  }
  RegisterCuClasses(unit_, class_names_, cu_scope_names_,
                    parameterized_class_names_);
  RegisterAnonymousProgramNames(unit_, anonymous_program_names_);
  RegisterPackageParams(unit_, cu_param_scope_, arena_);
  RegisterClassParams(unit_, cu_param_scope_, arena_, diag_);
  RegisterPackageTypedefs(unit_, typedefs_, arena_);
  RegisterClassTypedefs(unit_, typedefs_, arena_);
  // §13.3 with §7.2.1: after the two registrations above, which are what give
  // the table the "pkg::T" and "Class::T" names a formal's member may be
  // written with; a package's and a compilation-unit class's subroutines are
  // reached by no module's item walk (elaborator_items_formals.cpp).
  ResolveUnitScopeFormalTypes(unit_, typedefs_, arena_);
  // Seed the unions ItemElaborationStateSaver folds each module's entries into.
  // A compilation unit with no module to elaborate never reaches that fold, and
  // the passes reading the unions afterwards still have to see what the
  // compilation unit itself declared (§3.12.1).
  all_typedefs_ = typedefs_;
  all_cu_param_scope_ = cu_param_scope_;
}

std::optional<ModuleDecl*> Elaborator::ResolveCellUseOverride(
    std::string_view name) const {
  // A cell clause of a config an instance was handed to is the nearer rule for
  // the instances beneath that one (§33.4.2).
  for (const auto& dov : delegated_cell_use_overrides_) {
    if (dov.cell != name || !config_inst_path_.starts_with(dov.subtree + ".") ||
        !CellUseOverrideApplies(dov.use.src_lib, name, unit_)) {
      continue;
    }
    std::string_view lib = dov.use.use_lib.empty()
                               ? std::string_view(current_library_)
                               : std::string_view(dov.use.use_lib);
    return FindCellInLibrary(lib, dov.use.use_cell, unit_);
  }
  auto it = cell_clause_use_overrides_.find(std::string(name));
  if (it == cell_clause_use_overrides_.end()) return std::nullopt;
  const auto& ov = it->second;

  // A library-qualified cell clause applies only to the cell as defined in
  // that library (§33.4.1.4); if no such cell exists the clause matches
  // nothing and resolution proceeds normally.
  if (!CellUseOverrideApplies(ov.src_lib, name, unit_)) return std::nullopt;

  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  return FindCellInLibrary(target_lib, ov.use_cell, unit_);
}

std::optional<ModuleDecl*> Elaborator::ResolveInstanceBindOverride() const {
  if (config_inst_path_.empty()) return std::nullopt;
  for (const auto& [path, ulib, ucell] : instance_bind_overrides_) {
    if (path != config_inst_path_) continue;
    // An omitted target library is inherited from the parent cell (§33.4.1.6).
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
  const std::vector<std::string>* libs =
      InstanceLiblistForPath(path, instance_liblist_overrides_);
  if (libs == nullptr) {
    auto it = cell_clause_liblist_overrides_.find(std::string(name));
    if (it != cell_clause_liblist_overrides_.end()) libs = &it->second;
  }
  std::string_view which = "library list";
  if (libs == nullptr &&
      SelectedLibraryListInForce(library_order_, library_order_strict_)) {
    libs = &library_order_;
    which = "default library list";
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

const std::vector<std::string>* InstanceLiblistForPath(
    const std::string& inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        overrides) {
  if (inst_path.empty()) return nullptr;
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
  return inherited;
}

// §33.4.1.4, §33.4.1.5: selects the library list that governs resolution of
// `name`, preferring the most specific instance-scoped liblist rule and falling
// back to a cell-clause liblist. Returns nullptr when no liblist clause
// applies.
static const std::vector<std::string>* SelectOverrideLiblist(
    std::string_view name, const std::string& current_inst_path,
    const std::vector<std::pair<std::string, std::vector<std::string>>>&
        instance_liblist_overrides,
    const std::unordered_map<std::string, std::vector<std::string>>&
        cell_clause_liblist_overrides) {
  const std::vector<std::string>* override_liblist =
      InstanceLiblistForPath(current_inst_path, instance_liblist_overrides);

  // Absent an instance-scoped library list, a cell selection clause may name
  // the library list for this cell (§33.4.1.4, §33.4.1.5).
  if (override_liblist == nullptr) {
    if (auto it = cell_clause_liblist_overrides.find(std::string(name));
        it != cell_clause_liblist_overrides.end()) {
      override_liblist = &it->second;
    }
  }
  return override_liblist;
}

// Chooses among `candidates` using the global library order, applying strict
// library-order filtering and the config-elaboration parent-library preference
// (§33.4.1.5). Returns nullptr when no candidate survives filtering.
static ModuleDecl* PickCandidateByGlobalOrder(
    std::vector<ModuleDecl*> candidates,
    const std::vector<std::string>& library_order, bool library_order_strict,
    bool in_config_elaboration, std::string_view current_library) {
  // An empty selected library list selects no libraries to filter against;
  // it is treated here as no list being selected (§33.4.1.5).
  bool list_in_force =
      SelectedLibraryListInForce(library_order, library_order_strict);
  if (list_in_force && !candidates.empty()) {
    candidates = FilterCandidatesByLibrary(candidates, library_order);
  }
  if (candidates.empty()) return nullptr;

  // §33.4.1.5: when no library list clause is selected (or the selected
  // list is empty), the list holds only the parent cell's library, so an
  // instance binds to the cell defined in its parent's library.
  bool no_list_selected = !list_in_force;
  if (in_config_elaboration && no_list_selected && !current_library.empty()) {
    for (auto* c : candidates) {
      if (c->library == current_library) return c;
    }
  }
  return PickByLibraryOrder(candidates, library_order);
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  if (auto hit = FindInstanceUseOverride(config_inst_path_,
                                         instance_use_overrides_, unit_);
      hit.has_value()) {
    return *hit;
  }

  // §33.4.1.6: an instance selection is more specific than a cell selection, so
  // a plain instance use binding is applied before any cell-clause use.
  if (auto hit = ResolveInstanceBindOverride(); hit.has_value()) {
    return *hit;
  }

  // §33.6.3: a cell selection clause's use expansion binds every cell of the
  // selected name to the one library.cell it names, so the binding is settled
  // here rather than by the search below. The position is the rule and not an
  // ordering of convenience: a configuration may name a cell in a library its
  // own default clause leaves off the list, and that cell is still what the
  // name binds, because naming a description is not asking for a search that a
  // library list could exclude it from.
  if (auto hit = ResolveCellUseOverride(name); hit.has_value()) {
    return *hit;
  }

  ModuleDecl* extern_decl = nullptr;
  std::vector<ModuleDecl*> candidates;
  CollectModuleCandidates(name, unit_, candidates, extern_decl);

  const std::vector<std::string>* override_liblist = SelectOverrideLiblist(
      name, config_inst_path_, instance_liblist_overrides_,
      cell_clause_liblist_overrides_);

  // §33.6.2: a library the default clause's list leaves out is not searched at
  // all, so a description held only there is not used. Filtering against that
  // list can therefore empty a candidate set that was not empty, and a name
  // whose every description the list excluded has reached no cell -- the
  // last-resort search below consults no list and would otherwise hand back
  // exactly the description the list excluded.
  //
  // The exclusion is the default clause's own, so it holds however the search
  // for this name proceeded. A cell clause or an instance clause naming a
  // narrower list decides which of the libraries still in play answers, and
  // finding nothing in that narrower list leaves the name unanswered; it does
  // not put back the libraries the default clause left out.
  bool selected_list_governed =
      SelectedLibraryListInForce(library_order_, library_order_strict_);
  if (override_liblist != nullptr && !candidates.empty()) {
    candidates = FilterCandidatesByLibrary(candidates, *override_liblist);
    if (!candidates.empty()) {
      return PickByLibraryOrder(candidates, *override_liblist);
    }
  } else {
    if (ModuleDecl* picked = PickCandidateByGlobalOrder(
            std::move(candidates), library_order_, library_order_strict_,
            in_config_elaboration_, current_library_)) {
      return picked;
    }
  }
  if (extern_decl) return extern_decl;
  if (selected_list_governed) return nullptr;

  return FindNonModuleDesign(name, unit_);
}

ModuleDecl* Elaborator::FindDesignCell(std::string_view library,
                                       std::string_view cell,
                                       bool qualified_in_source) const {
  if (library.empty()) return FindModule(cell);
  ModuleDecl* in_library = FindCellInLibrary(library, cell, unit_);
  if (in_library != nullptr || qualified_in_source) return in_library;
  return FindModule(cell);
}

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  return FindModule(name);
}

}  // namespace delta
