#include "elaborator/dollar_scope.h"

#include <algorithm>
#include <cstddef>
#include <deque>
#include <string_view>
#include <vector>

#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kClassDepth = 16;

struct SpecArg {
  std::string_view name;
  const Expr* value = nullptr;
  const DataType* type = nullptr;
};

struct Specialization {
  std::vector<SpecArg> args;
  const DollarScope* where = nullptr;
};

struct FoundClass {
  const ClassDecl* cls = nullptr;
  Specialization spec;
  const DollarScope* home = nullptr;
};

struct ClassRef {
  std::string_view scope;
  std::string_view name;
  const std::vector<DataType>& args;
};

struct ClassQuery {
  const DollarParams& params;
  std::deque<DollarScope>& built;
};

}  // namespace

NameRole RoleOf(const DollarScope* scope, std::string_view name) {
  for (; scope != nullptr; scope = scope->outer) {
    if (scope->non_queues.count(name) != 0) return NameRole::kNonQueue;
    if (scope->others.count(name) != 0) return NameRole::kOther;
    if (scope->dollar_params.count(name) != 0) return NameRole::kDollarParam;
  }
  return NameRole::kUnknown;
}

static std::string_view ScopedDollarParam(std::string_view scope_name,
                                          std::string_view name,
                                          const DollarParams& params) {
  return params.scoped.count({scope_name, name}) != 0 ? name
                                                      : std::string_view{};
}

static std::string_view NamedAt(const Expr* e, const DollarScope& scope,
                                ClassQuery& query, int depth);

static bool HoldsDollar(const Expr* value, const DollarScope& where,
                        ClassQuery& query, int depth) {
  return value != nullptr &&
         (IsLoneDollar(value) || !NamedAt(value, where, query, depth).empty());
}

static void NoteParamAt(std::string_view name, const Expr* value,
                        ClassQuery& query, int depth, DollarScope& scope) {
  const bool kHoldsDollar = HoldsDollar(value, scope, query, depth);
  (kHoldsDollar ? scope.dollar_params : scope.others).insert(name);
}

static bool DeclaresTypeName(const ModuleItem* item) {
  const bool kTypeItem = item->kind == ModuleItemKind::kTypedef ||
                         (item->kind == ModuleItemKind::kParamDecl &&
                          item->data_type.kind == DataTypeKind::kVoid);
  return kTypeItem && item->typedef_type.kind == DataTypeKind::kNamed;
}

static std::string_view ClassItemName(const ModuleItem* item) {
  if (item->class_decl != nullptr) return item->class_decl->name;
  return DeclaresTypeName(item) ? item->name : std::string_view{};
}

static void NoteClassItem(const ModuleItem* item, DollarScope& scope) {
  const std::string_view kName = ClassItemName(item);
  if (kName.empty()) return;
  scope.classes.insert_or_assign(
      kName, item->class_decl != nullptr
                 ? DollarClass{item->class_decl}
                 : DollarClass{nullptr, &item->typedef_type});
}

static FoundClass ClassOfPrefix(const Expr* prefix, const DollarScope& scope,
                                ClassQuery& query, int depth);

static FoundClass ClassOfRef(const ClassRef& ref, const DollarScope& from,
                             ClassQuery& query, int depth);

static void NoteClassMembers(const FoundClass& found, ClassQuery& query,
                             int depth, DollarScope& into);

static const DollarScope& PackageScope(const PackageDecl* pkg,
                                       ClassQuery& query, int depth);

static const DollarScope& UnitScope(ClassQuery& query, int depth);

static FoundClass ClassFrom(const DollarClass& entry, std::string_view name,
                            const DollarScope& found_in, ClassQuery& query,
                            int depth);

static FoundClass ClassInChain(std::string_view name, const DollarScope& from,
                               ClassQuery& query, int depth) {
  for (const DollarScope* s = &from; s != nullptr; s = s->outer) {
    const auto kIt = s->classes.find(name);
    if (kIt != s->classes.end())
      return ClassFrom(kIt->second, name, *s, query, depth);
  }
  return {};
}

static FoundClass ClassFrom(const DollarClass& entry, std::string_view name,
                            const DollarScope& found_in, ClassQuery& query,
                            int depth) {
  if (depth > kClassDepth) return {};
  if (entry.package != nullptr) {
    return ClassInChain(name, PackageScope(entry.package, query, depth), query,
                        depth + 1);
  }
  const DollarScope& from = entry.where != nullptr ? *entry.where : found_in;
  if (entry.alias != nullptr) {
    const DataType& type = *entry.alias;
    return ClassOfRef({type.scope_name, type.type_name, type.type_params}, from,
                      query, depth + 1);
  }
  if (entry.prefix != nullptr)
    return ClassOfPrefix(entry.prefix, from, query, depth + 1);
  return {entry.cls, {}, &from};
}

static const DollarScope* MembersOf(const FoundClass& found, ClassQuery& query,
                                    int depth) {
  if (found.cls == nullptr) return nullptr;
  DollarScope& members = query.built.emplace_back();
  members.outer = found.home;
  NoteClassMembers(found, query, depth, members);
  return &members;
}

static FoundClass NestedClass(const FoundClass& outer, std::string_view name,
                              ClassQuery& query, int depth) {
  const DollarScope* members = MembersOf(outer, query, depth + 1);
  if (members == nullptr) return {};
  const auto kIt = members->classes.find(name);
  if (kIt == members->classes.end()) return {};
  return ClassFrom(kIt->second, name, *members, query, depth + 1);
}

static const DollarScope* NamedPackageScope(std::string_view name,
                                            ClassQuery& query, int depth) {
  const auto kPackage = query.params.packages.find(name);
  if (kPackage == query.params.packages.end()) return nullptr;
  return &PackageScope(kPackage->second, query, depth);
}

static FoundClass ClassWithinNamed(std::string_view scope_name,
                                   std::string_view name,
                                   const DollarScope& from, ClassQuery& query,
                                   int depth) {
  if (scope_name.empty()) return ClassInChain(name, from, query, depth);
  const DollarScope* package_scope =
      NamedPackageScope(scope_name, query, depth);
  if (package_scope != nullptr)
    return ClassInChain(name, *package_scope, query, depth);
  return NestedClass(ClassInChain(scope_name, from, query, depth), name, query,
                     depth);
}

static std::vector<SpecArg> ArgsOfTypes(const std::vector<DataType>& types) {
  std::vector<SpecArg> args;
  args.reserve(types.size());
  for (const DataType& type : types) {
    args.push_back({type.param_arg_name,
                    type.type_name.empty() ? type.type_ref_expr : nullptr,
                    &type});
  }
  return args;
}

static std::vector<SpecArg> ArgsOfPrefix(const Expr* prefix) {
  std::vector<SpecArg> args;
  args.reserve(prefix->elements.size());
  for (size_t k = 0; k < prefix->elements.size(); ++k)
    args.push_back({prefix->arg_names[k], prefix->elements[k]});
  return args;
}

static FoundClass ClassOfRef(const ClassRef& ref, const DollarScope& from,
                             ClassQuery& query, int depth) {
  FoundClass found = ClassWithinNamed(ref.scope, ref.name, from, query, depth);
  if (!ref.args.empty()) found.spec = {ArgsOfTypes(ref.args), &from};
  return found;
}

static FoundClass ClassWithin(const Expr* outer, std::string_view name,
                              const DollarScope& scope, ClassQuery& query,
                              int depth) {
  const DollarScope* package_scope =
      outer->kind == ExprKind::kIdentifier
          ? NamedPackageScope(outer->text, query, depth)
          : nullptr;
  if (package_scope != nullptr)
    return ClassInChain(name, *package_scope, query, depth);
  return NestedClass(ClassOfPrefix(outer, scope, query, depth), name, query,
                     depth);
}

static FoundClass ClassOfPrefix(const Expr* prefix, const DollarScope& scope,
                                ClassQuery& query, int depth) {
  FoundClass found;
  if (prefix->kind == ExprKind::kMemberAccess) {
    found = ClassWithin(prefix->lhs, prefix->rhs->text, scope, query, depth);
  } else {
    const DollarScope& from =
        prefix->scope_prefix.empty() ? scope : UnitScope(query, depth);
    found = ClassInChain(prefix->text, from, query, depth);
  }
  if (prefix->has_param_spec) found.spec = {ArgsOfPrefix(prefix), &scope};
  return found;
}

static const SpecArg* ArgFor(const Specialization& spec, size_t i,
                             std::string_view name) {
  if (i < spec.args.size() && spec.args[i].name.empty()) return &spec.args[i];
  const auto kNamed = std::ranges::find(spec.args, name, &SpecArg::name);
  return kNamed != spec.args.end() ? &*kNamed : nullptr;
}

static DollarClass TypeParamClass(const DataType& fallback, const SpecArg* arg,
                                  const DollarScope* where) {
  if (arg == nullptr) return {nullptr, &fallback};
  return {nullptr, arg->type, arg->value, nullptr, where};
}

static void NotePortParams(const FoundClass& found, ClassQuery& query,
                           int depth, DollarScope& into) {
  const ClassDecl* cls = found.cls;
  for (size_t i = 0; i < cls->params.size(); ++i) {
    const auto& [name, value] = cls->params[i];
    const SpecArg* arg = cls->localparam_port_names.count(name) != 0
                             ? nullptr
                             : ArgFor(found.spec, i, name);
    if (cls->type_param_names.count(name) != 0) {
      into.classes.insert_or_assign(
          name, TypeParamClass(cls->param_types[i], arg, found.spec.where));
      into.others.insert(name);
    } else if (arg != nullptr) {
      const bool kHoldsDollar =
          HoldsDollar(arg->value, *found.spec.where, query, depth);
      (kHoldsDollar ? into.dollar_params : into.others).insert(name);
    } else {
      NoteParamAt(name, value, query, depth, into);
    }
  }
}

static void Forget(std::string_view name, DollarScope& scope) {
  scope.non_queues.erase(name);
  scope.others.erase(name);
  scope.dollar_params.erase(name);
  scope.classes.erase(name);
}

static std::string_view MemberName(const ClassMember* m) {
  if (m->typedef_item != nullptr) return m->typedef_item->name;
  return m->nested_class != nullptr ? m->nested_class->name : m->name;
}

static void NoteInheritedNames(const ClassDecl* cls, const DollarScope& ports,
                               ClassQuery& query, int depth,
                               DollarScope& into) {
  if (cls->base_class.empty()) return;
  const ClassRef kBase{cls->base_class_scope, cls->base_class,
                       cls->base_class_type_params};
  const DollarScope* base_names =
      MembersOf(ClassOfRef(kBase, ports, query, depth + 1), query, depth + 1);
  if (base_names == nullptr) return;
  into.non_queues = base_names->non_queues;
  into.others = base_names->others;
  into.dollar_params = base_names->dollar_params;
  for (const auto& [name, entry] : base_names->classes) {
    DollarClass inherited = entry;
    if (inherited.where == nullptr) inherited.where = base_names;
    into.classes.emplace(name, inherited);
  }
  for (const auto& [name, value] : cls->params) Forget(name, into);
  for (const ClassMember* m : cls->members) Forget(MemberName(m), into);
}

static void NoteBodyNames(const ClassDecl* cls, ClassQuery& query, int depth,
                          DollarScope& into) {
  for (const ClassMember* m : cls->members) {
    if (m->nested_class != nullptr) {
      into.classes.insert_or_assign(m->nested_class->name,
                                    DollarClass{m->nested_class});
    }
    if (m->typedef_item != nullptr) NoteClassItem(m->typedef_item, into);
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (m->is_param) {
      NoteParamAt(m->name, m->init_expr, query, depth, into);
    } else {
      NoteDeclaredName(m->name, m->data_type, m->unpacked_dims, into);
    }
  }
}

static void NoteClassMembers(const FoundClass& found, ClassQuery& query,
                             int depth, DollarScope& into) {
  DollarScope& ports = query.built.emplace_back();
  ports.outer = into.outer;
  NotePortParams(found, query, depth, ports);
  NoteInheritedNames(found.cls, ports, query, depth, into);
  NotePortParams(found, query, depth, into);
  NoteBodyNames(found.cls, query, depth, into);
}

static bool ClassMemberHoldsDollar(const Expr* e, const DollarScope& scope,
                                   ClassQuery& query, int depth) {
  const DollarScope* members = MembersOf(
      ClassOfPrefix(e->lhs, scope, query, depth + 1), query, depth + 1);
  return members != nullptr && members->dollar_params.count(e->rhs->text) != 0;
}

static std::string_view NamedAt(const Expr* e, const DollarScope& scope,
                                ClassQuery& query, int depth) {
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty())
    return ScopedDollarParam(e->scope_prefix, e->text, query.params);
  if (e->kind == ExprKind::kIdentifier)
    return RoleOf(&scope, e->text) == NameRole::kDollarParam
               ? e->text
               : std::string_view{};
  if (e->kind != ExprKind::kMemberAccess || !e->is_scope_resolution) return {};
  const std::string_view kPackaged =
      e->lhs->kind == ExprKind::kIdentifier
          ? ScopedDollarParam(e->lhs->text, e->rhs->text, query.params)
          : std::string_view{};
  if (!kPackaged.empty()) return kPackaged;
  return ClassMemberHoldsDollar(e, scope, query, depth) ? e->rhs->text
                                                        : std::string_view{};
}

std::string_view DollarParamNamed(const Expr* e, const DollarScope& scope,
                                  const DollarParams& params) {
  std::deque<DollarScope> built;
  ClassQuery query{params, built};
  return NamedAt(e, scope, query, 0);
}

std::string_view DollarParamNamed(const Expr* e, const DollarScan& scan) {
  return DollarParamNamed(e, scan.scope, scan.report.params);
}

void NoteDeclaredName(std::string_view name, const DataType& type,
                      const std::vector<Expr*>& dims, DollarScope& scope) {
  const bool kFixedFirst = !dims.empty() && !IsQueueDim(dims[0]);
  const bool kPlain = dims.empty() && type.kind != DataTypeKind::kNamed &&
                      type.type_ref_expr == nullptr;
  (kFixedFirst || kPlain ? scope.non_queues : scope.others).insert(name);
}

void NoteInstanceParam(std::string_view name, const InstanceParams& instance,
                       DollarScope& scope) {
  const bool kUnbounded = instance.unbounded.count(name) != 0;
  (kUnbounded ? scope.dollar_params : scope.others).insert(name);
  if (instance.overridden.count(name) != 0) scope.overridden.insert(name);
  const auto kType = instance.types.find(name);
  if (kType != instance.types.end())
    scope.classes.insert_or_assign(name, DollarClass{nullptr, kType->second});
}

static void NoteImportedClasses(const PackageDecl* pkg,
                                const ImportItem& import, DollarScope& scope) {
  for (const ModuleItem* item : pkg->items) {
    const std::string_view kName = ClassItemName(item);
    if (!kName.empty() && (import.is_wildcard || kName == import.item_name))
      scope.classes.emplace(kName, DollarClass{nullptr, nullptr, nullptr, pkg});
  }
}

static void NoteImport(const ImportItem& import, const DollarParams& params,
                       DollarScope& scope) {
  for (const auto& [package, name] : params.scoped) {
    if (package == import.package_name &&
        (import.is_wildcard || name == import.item_name)) {
      scope.dollar_params.insert(name);
    }
  }
  for (const auto& [name, pkg] : params.packages) {
    if (name == import.package_name) NoteImportedClasses(pkg, import, scope);
  }
}

bool NamesNonQueue(const DollarScope* scope, std::string_view name) {
  return RoleOf(scope, name) == NameRole::kNonQueue;
}

static void NoteItemName(const ModuleItem* item, const InstanceParams* instance,
                         ClassQuery& query, int depth, DollarScope& scope) {
  NoteClassItem(item, scope);
  if (item->kind == ModuleItemKind::kVarDecl ||
      item->kind == ModuleItemKind::kNetDecl) {
    NoteDeclaredName(item->name, item->data_type, item->unpacked_dims, scope);
  } else if (item->kind == ModuleItemKind::kImportDecl) {
    NoteImport(item->import_item, query.params, scope);
  } else if (item->kind != ModuleItemKind::kParamDecl) {
    return;
  } else if (instance != nullptr) {
    NoteInstanceParam(item->name, *instance, scope);
  } else {
    NoteParamAt(item->name, item->init_expr, query, depth, scope);
  }
}

static DollarTaker TakerDeclaredBy(const ModuleItem* item,
                                   const PackageDecl* package) {
  const ModuleDecl* nested = item->nested_module_decl;
  if (nested != nullptr && nested->decl_kind == ModuleDeclKind::kChecker)
    return {nullptr, nested, package};
  const bool kAssertion = item->kind == ModuleItemKind::kSequenceDecl ||
                          item->kind == ModuleItemKind::kPropertyDecl;
  return {kAssertion ? item : nullptr, nullptr, package};
}

static std::string_view TakerName(const DollarTaker& taker) {
  if (taker.checker != nullptr) return taker.checker->name;
  return taker.decl != nullptr ? taker.decl->name : std::string_view{};
}

static void NoteItemNamesAt(const std::vector<ModuleItem*>& items,
                            const InstanceParams* instance, ClassQuery& query,
                            int depth, DollarScope& scope) {
  for (const ModuleItem* item : items) {
    NoteItemName(item, instance, query, depth, scope);
    scope.takers.insert(TakerName(TakerDeclaredBy(item, nullptr)));
  }
}

void NoteItemNames(const std::vector<ModuleItem*>& items,
                   const DollarParams& params, const InstanceParams* instance,
                   DollarScope& scope) {
  std::deque<DollarScope> built;
  ClassQuery query{params, built};
  NoteItemNamesAt(items, instance, query, 0, scope);
}

static void NoteUnitNamesAt(const CompilationUnit& unit, ClassQuery& query,
                            int depth, DollarScope& scope) {
  for (const ClassDecl* cls : unit.classes)
    scope.classes.insert_or_assign(cls->name, DollarClass{cls});
  NoteItemNamesAt(unit.cu_items, nullptr, query, depth, scope);
}

void NoteUnitNames(const CompilationUnit& unit, const DollarParams& params,
                   DollarScope& scope) {
  std::deque<DollarScope> built;
  ClassQuery query{params, built};
  NoteUnitNamesAt(unit, query, 0, scope);
}

static const DollarScope& PackageScope(const PackageDecl* pkg,
                                       ClassQuery& query, int depth) {
  const DollarParams& params = query.params;
  const auto kCached = params.package_scopes.find(pkg);
  if (kCached != params.package_scopes.end()) return *kCached->second;
  DollarScope& scope = params.cached.emplace_back();
  params.package_scopes.emplace(pkg, &scope);
  NoteItemNamesAt(pkg->items, nullptr, query, depth + 1, scope);
  return scope;
}

static const DollarScope& UnitScope(ClassQuery& query, int depth) {
  const DollarParams& params = query.params;
  if (params.unit_scope != nullptr) return *params.unit_scope;
  DollarScope& scope = params.cached.emplace_back();
  params.unit_scope = &scope;
  NoteUnitNamesAt(*params.unit, query, depth + 1, scope);
  return scope;
}

void NoteClassNames(const ClassDecl* cls, const DollarParams& params,
                    DollarClassStore& store, DollarScope& scope) {
  ClassQuery query{params, store.scopes};
  NoteClassMembers({cls, {}, scope.outer}, query, 0, scope);
}

static void AddScopedDollarParams(std::string_view scope_name,
                                  const std::vector<ModuleItem*>& items,
                                  const DollarScope& scope,
                                  DollarParams& params) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        scope.dollar_params.count(item->name) != 0) {
      params.scoped.emplace(scope_name, item->name);
    }
  }
}

DollarParams UnitDollarParams(const CompilationUnit& unit) {
  DollarParams params;
  params.unit = &unit;
  for (const PackageDecl* pkg : unit.packages)
    params.packages.emplace(pkg->name, pkg);
  for (const PackageDecl* pkg : unit.packages) {
    DollarScope scope;
    NoteItemNames(pkg->items, params, nullptr, scope);
    AddScopedDollarParams(pkg->name, pkg->items, scope, params);
  }
  DollarScope unit_scope;
  NoteUnitNames(unit, params, unit_scope);
  AddScopedDollarParams("$unit", unit.cu_items, unit_scope, params);
  params.package_scopes.clear();
  params.unit_scope = nullptr;
  return params;
}

void NoteLocalNames(const Stmt* s, DollarScope& scope) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    NoteDeclaredName(s->var_name, s->var_decl_type, s->var_unpacked_dims,
                     scope);
  }
  ForEachChildStmt(s,
                   [&scope](Stmt* const& sub) { NoteLocalNames(sub, scope); });
}

void AddDollarTakers(const std::vector<ModuleItem*>& items,
                     const PackageDecl* package, DollarTakers& takers) {
  for (const ModuleItem* item : items) {
    const DollarTaker kTaker = TakerDeclaredBy(item, package);
    const std::string_view kName = TakerName(kTaker);
    if (!kName.empty()) takers.insert_or_assign(kName, kTaker);
    AddDollarTakers(item->clocking_decls, package, takers);
    for (const ModuleItem* arm = item; arm != nullptr; arm = arm->gen_else)
      AddDollarTakers(arm->gen_body, package, takers);
    for (const GenerateCaseItem& arm : item->gen_case_items)
      AddDollarTakers(arm.body, package, takers);
  }
}

DollarTakers UnitDollarTakers(const CompilationUnit& unit) {
  DollarTakers takers;
  for (const PackageDecl* pkg : unit.packages)
    AddDollarTakers(pkg->items, pkg, takers);
  for (const ModuleDecl* checker : unit.checkers)
    takers.insert_or_assign(checker->name, DollarTaker{nullptr, checker});
  AddDollarTakers(unit.cu_items, nullptr, takers);
  return takers;
}

static const DollarScope& HomeScope(const DollarScope& from,
                                    std::string_view name) {
  const DollarScope* home = &from;
  while (home->takers.count(name) == 0 && home->outer != nullptr)
    home = home->outer;
  return *home;
}

std::string_view DefaultDollarParam(const Expr* value,
                                    std::string_view taker_name,
                                    const DollarTaker& taker,
                                    const DollarScan& scan) {
  const DollarParams& params = scan.report.params;
  if (taker.package == nullptr)
    return DollarParamNamed(value, HomeScope(scan.scope, taker_name), params);
  DollarScope home;
  NoteItemNames(taker.package->items, params, nullptr, home);
  return DollarParamNamed(value, home, params);
}

}  // namespace delta
