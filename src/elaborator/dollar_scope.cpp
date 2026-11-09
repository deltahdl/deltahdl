#include "elaborator/dollar_scope.h"

#include <algorithm>
#include <cstddef>
#include <deque>
#include <set>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/dollar_contexts.h"
#include "elaborator/dollar_scope_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

constexpr int kClassDepth = 16;

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

static bool IsTypeParam(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kParamDecl &&
         item->data_type.kind == DataTypeKind::kVoid;
}

static bool DeclaresTypeName(const ModuleItem* item) {
  const bool kTypeItem =
      item->kind == ModuleItemKind::kTypedef || IsTypeParam(item);
  return kTypeItem && item->typedef_type.kind == DataTypeKind::kNamed;
}

static bool DeclaresAType(const ModuleItem* item) {
  const DataType& type = item->typedef_type;
  const bool kWritten =
      type.kind != DataTypeKind::kImplicit || type.type_ref_expr != nullptr;
  return IsTypeParam(item) ||
         (item->kind == ModuleItemKind::kTypedef && kWritten);
}

static void NoteEnumConstants(const DataType& type, DollarScope& scope) {
  for (const EnumMember& member : type.enum_members) {
    if (member.range_start != nullptr) {
      scope.numbered_enums.push_back(&member);
    } else {
      scope.non_queues.insert(member.name);
    }
  }
}

static void NoteTypeItem(const ModuleItem* item, DollarScope& scope) {
  if (!DeclaresAType(item)) return;
  scope.types.insert_or_assign(
      item->name, DollarType{&item->typedef_type, &item->unpacked_dims});
  NoteEnumConstants(item->typedef_type, scope);
}

static void NoteParamType(std::string_view name, const DataType& type,
                          const std::vector<Expr*>* dims, const Expr* value,
                          DollarScope& scope) {
  const bool kTyped = type.kind != DataTypeKind::kImplicit ||
                      type.packed_dim_left != nullptr || type.signing_written ||
                      (dims != nullptr && !dims->empty());
  if (kTyped) {
    scope.typed_vars.insert_or_assign(name, DollarType{&type, dims});
  } else if (value != nullptr) {
    scope.param_values.insert_or_assign(name, value);
  }
}

static const std::vector<Expr*>* PortDims(
    const std::unordered_map<std::string_view, std::vector<Expr*>>& dims,
    std::string_view name) {
  const auto kDims = dims.find(name);
  return kDims != dims.end() ? &kDims->second : nullptr;
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

static void NoteClassMembers(const FoundClass& found, ClassQuery& query,
                             int depth, DollarScope& into);

static FoundClass ClassFrom(const DollarClass& entry, std::string_view name,
                            const DollarScope& found_in, ClassQuery& query,
                            int depth);

FoundClass ClassInChain(std::string_view name, const DollarScope* from,
                        ClassQuery& query, int depth) {
  for (const DollarScope* s = from; s != nullptr; s = s->outer) {
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
    return ClassInChain(name, &PackageScope(entry.package, query, depth), query,
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

const DollarScope* MembersOf(const FoundClass& found, ClassQuery& query,
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

const DollarScope* NamedPackageScope(std::string_view name, ClassQuery& query,
                                     int depth) {
  const auto kPackage = query.params.packages.find(name);
  if (kPackage == query.params.packages.end()) return nullptr;
  return &PackageScope(kPackage->second, query, depth);
}

static FoundClass ClassWithinNamed(std::string_view scope_name,
                                   std::string_view name,
                                   const DollarScope& from, ClassQuery& query,
                                   int depth) {
  if (scope_name.empty()) return ClassInChain(name, &from, query, depth);
  const DollarScope* package_scope =
      NamedPackageScope(scope_name, query, depth);
  if (package_scope != nullptr)
    return ClassInChain(name, package_scope, query, depth);
  return NestedClass(ClassInChain(scope_name, &from, query, depth), name, query,
                     depth);
}

std::vector<SpecArg> ArgsOfTypes(const std::vector<DataType>& types) {
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

FoundClass ClassOfRef(const ClassRef& ref, const DollarScope& from,
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
    return ClassInChain(name, package_scope, query, depth);
  return NestedClass(ClassOfPrefix(outer, scope, query, depth), name, query,
                     depth);
}

FoundClass ClassOfPrefix(const Expr* prefix, const DollarScope& scope,
                         ClassQuery& query, int depth) {
  FoundClass found;
  if (prefix->kind == ExprKind::kMemberAccess) {
    found = ClassWithin(prefix->lhs, prefix->rhs->text, scope, query, depth);
  } else {
    const DollarScope& from =
        prefix->scope_prefix.empty() ? scope : UnitScope(query, depth);
    found = ClassInChain(prefix->text, &from, query, depth);
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

static void NoteClassTypeParam(std::string_view name, const DataType* fallback,
                               const SpecArg* arg, const DollarScope* where,
                               DollarScope& into) {
  const DollarType kBound = arg != nullptr
                                ? DollarType{arg->type, nullptr, nullptr, where}
                                : DollarType{fallback};
  into.types.insert_or_assign(name, kBound);
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
      const bool kKeepsDefault = found.spec.where != nullptr ||
                                 cls->localparam_port_names.count(name) != 0;
      NoteClassTypeParam(name, kKeepsDefault ? &cls->param_types[i] : nullptr,
                         arg, found.spec.where, into);
    } else if (arg != nullptr) {
      const bool kHoldsDollar =
          HoldsDollar(arg->value, *found.spec.where, query, depth);
      (kHoldsDollar ? into.dollar_params : into.others).insert(name);
      NoteParamType(name, cls->param_types[i],
                    PortDims(cls->param_port_unpacked_dims, name), nullptr,
                    into);
    } else {
      NoteParamAt(name, value, query, depth, into);
      NoteParamType(name, cls->param_types[i],
                    PortDims(cls->param_port_unpacked_dims, name), value, into);
    }
  }
}

static void InheritTypes(
    const std::unordered_map<std::string_view, DollarType>& base,
    const DollarScope* base_scope,
    std::unordered_map<std::string_view, DollarType>& into) {
  for (const auto& [name, entry] : base) {
    DollarType inherited = entry;
    if (inherited.where == nullptr) inherited.where = base_scope;
    into.emplace(name, inherited);
  }
}

static void Forget(std::string_view name, DollarScope& scope) {
  scope.non_queues.erase(name);
  scope.others.erase(name);
  scope.dollar_params.erase(name);
  scope.classes.erase(name);
  scope.types.erase(name);
  scope.typed_vars.erase(name);
  scope.param_values.erase(name);
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
  into.base = base_names;
  into.non_queues = base_names->non_queues;
  into.others = base_names->others;
  into.dollar_params = base_names->dollar_params;
  into.param_values = base_names->param_values;
  into.numbered_enums = base_names->numbered_enums;
  InheritTypes(base_names->typed_vars, base_names, into.typed_vars);
  InheritTypes(base_names->types, base_names, into.types);
  for (const auto& [name, entry] : base_names->classes) {
    DollarClass inherited = entry;
    if (inherited.where == nullptr) inherited.where = base_names;
    into.classes.emplace(name, inherited);
  }
  for (const auto& [name, value] : cls->params) Forget(name, into);
  for (const ClassMember* m : cls->members) Forget(MemberName(m), into);
}

static void NoteBodyNames(const FoundClass& found, ClassQuery& query, int depth,
                          DollarScope& into) {
  const bool kValuesKnown =
      found.spec.args.empty() || !found.cls->params.empty();
  for (const ClassMember* m : found.cls->members) {
    if (m->nested_class != nullptr) {
      into.classes.insert_or_assign(m->nested_class->name,
                                    DollarClass{m->nested_class});
    }
    if (m->typedef_item != nullptr) {
      NoteClassItem(m->typedef_item, into);
      NoteTypeItem(m->typedef_item, into);
    }
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (m->is_param) {
      NoteParamAt(m->name, m->init_expr, query, depth, into);
      NoteParamType(m->name, m->data_type, &m->unpacked_dims,
                    kValuesKnown ? m->init_expr : nullptr, into);
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
  NoteBodyNames(found, query, depth, into);
  into.cls = found.cls;
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
  scope.typed_vars.insert_or_assign(name, DollarType{&type, &dims});
  NoteEnumConstants(type, scope);
}

void NoteInstanceParam(std::string_view name, const InstanceParams& instance,
                       DollarScope& scope) {
  const bool kUnbounded = instance.unbounded.count(name) != 0;
  (kUnbounded ? scope.dollar_params : scope.others).insert(name);
  if (instance.overridden.count(name) != 0) scope.overridden.insert(name);
  const auto kType = instance.types.find(name);
  if (kType == instance.types.end()) return;
  scope.classes.insert_or_assign(name, DollarClass{nullptr, kType->second});
  scope.types.insert_or_assign(name, DollarType{kType->second});
}

static void NoteImportedClasses(const PackageDecl* pkg,
                                const ImportItem& import, DollarScope& scope) {
  for (const ModuleItem* item : pkg->items) {
    const std::string_view kName = ClassItemName(item);
    if (!kName.empty() && (import.is_wildcard || kName == import.item_name))
      scope.classes.emplace(kName, DollarClass{nullptr, nullptr, nullptr, pkg});
  }
}

static void NoteImportedTypes(const PackageDecl* pkg, const ImportItem& import,
                              DollarScope& scope) {
  for (const ModuleItem* item : pkg->items) {
    if (!DeclaresAType(item)) continue;
    if (!import.is_wildcard && item->name != import.item_name) continue;
    scope.types.emplace(
        item->name, DollarType{&item->typedef_type, &item->unpacked_dims, pkg});
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
    if (name != import.package_name) continue;
    NoteImportedClasses(pkg, import, scope);
    NoteImportedTypes(pkg, import, scope);
    scope.imports.push_back(
        {pkg, import.is_wildcard ? std::string_view{} : import.item_name});
  }
}

static ClassRef SpecializedClassRef(const DataType& written) {
  if (!written.scope_param_assignment_written)
    return {written.scope_name, written.type_name, written.type_params};
  const std::string_view kOuter = written.outer_scope_names.empty()
                                      ? std::string_view{}
                                      : written.outer_scope_names.back();
  return {kOuter, written.scope_name, written.type_params};
}

const ClassDecl* NoteSpecializationNames(const DataType& written,
                                         const DollarScope& site,
                                         const DollarParams& params,
                                         DollarClassStore& store,
                                         DollarScope& scope) {
  if (written.kind != DataTypeKind::kNamed) return nullptr;
  ClassQuery query{params, store.scopes};
  FoundClass found = ClassOfRef(SpecializedClassRef(written), site, query, 0);
  if (found.cls == nullptr || found.cls->type_param_names.empty())
    return nullptr;
  if (found.spec.where == nullptr) found.spec.where = &site;
  scope.outer = found.home;
  NoteClassMembers(found, query, 0, scope);
  return found.cls;
}

static void NoteNamedBlock(const Stmt* s, DollarScope& scope) {
  if (s == nullptr || s->label.empty()) return;
  if (s->kind != StmtKind::kBlock && s->kind != StmtKind::kFork) return;
  scope.blocks.insert_or_assign(s->label, DollarBlock{{}, nullptr, s, {}});
}

static std::string_view GenvarOf(const ModuleItem* item) {
  return item->gen_init != nullptr ? item->gen_init->lhs->text
                                   : std::string_view{};
}

static void NoteGenerateBlocks(const ModuleItem* item, DollarScope& scope) {
  const std::string_view kGenvar = GenvarOf(item);
  for (const ModuleItem* arm = item; arm != nullptr; arm = arm->gen_else) {
    scope.blocks.insert_or_assign(
        arm->name, DollarBlock{{}, &arm->gen_body, nullptr, kGenvar});
  }
  for (const GenerateCaseItem& arm : item->gen_case_items) {
    scope.blocks.insert_or_assign(arm.label,
                                  DollarBlock{{}, &arm.body, nullptr, {}});
  }
}

static void NoteImplicitNet(const Expr* e, DollarScope& scope) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    scope.implicit_nets.insert(e->text);
  } else if (e->kind == ExprKind::kConcatenation) {
    for (const Expr* element : e->elements) NoteImplicitNet(element, scope);
  }
}

static void NoteItemScopes(const ModuleItem* item, DollarScope& scope) {
  switch (item->kind) {
    case ModuleItemKind::kModuleInst:
      scope.blocks.insert_or_assign(
          item->inst_name,
          DollarBlock{item->inst_module, nullptr, nullptr, {}});
      for (const auto& [port, actual] : item->inst_ports)
        NoteImplicitNet(actual, scope);
      break;
    case ModuleItemKind::kGenerateFor:
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
      NoteGenerateBlocks(item, scope);
      break;
    case ModuleItemKind::kContAssign:
      NoteImplicitNet(item->assign_lhs, scope);
      break;
    case ModuleItemKind::kGateInst:
      for (const Expr* terminal : item->gate_terminals)
        NoteImplicitNet(terminal, scope);
      break;
    default:
      NoteNamedBlock(item->body, scope);
      break;
  }
}

static bool ParamValueKnown(const ModuleItem* item,
                            const InstanceParams* instance) {
  return instance == nullptr || item->is_localparam ||
         (!instance->values_unknown &&
          instance->overridden.count(item->name) == 0);
}

static void NoteParamItem(const ModuleItem* item,
                          const InstanceParams* instance, ClassQuery& query,
                          int depth, DollarScope& scope) {
  if (instance != nullptr) {
    scope.types.erase(item->name);
    NoteInstanceParam(item->name, *instance, scope);
  } else {
    NoteParamAt(item->name, item->init_expr, query, depth, scope);
  }
  if (IsTypeParam(item)) return;
  NoteParamType(item->name, item->data_type, &item->unpacked_dims,
                ParamValueKnown(item, instance) ? item->init_expr : nullptr,
                scope);
}

static void NoteItemName(const ModuleItem* item, const InstanceParams* instance,
                         ClassQuery& query, int depth, DollarScope& scope) {
  NoteClassItem(item, scope);
  NoteTypeItem(item, scope);
  NoteItemScopes(item, scope);
  if (item->nested_module_decl != nullptr)
    scope.designs.insert_or_assign(item->nested_module_decl->name,
                                   item->nested_module_decl);
  if (item->kind == ModuleItemKind::kVarDecl ||
      item->kind == ModuleItemKind::kNetDecl) {
    NoteDeclaredName(item->name, item->data_type, item->unpacked_dims, scope);
  } else if (item->kind == ModuleItemKind::kImportDecl) {
    NoteImport(item->import_item, query.params, scope);
  } else if (item->kind == ModuleItemKind::kNettypeDecl ||
             item->kind == ModuleItemKind::kCovergroupDecl) {
    scope.non_queues.insert(item->name);
  } else if (item->kind == ModuleItemKind::kParamDecl) {
    NoteParamItem(item, instance, query, depth, scope);
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

void NoteItemNamesAt(const std::vector<ModuleItem*>& items,
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

const DollarScope& PackageScope(const PackageDecl* pkg, ClassQuery& query,
                                int depth) {
  const DollarParams& params = query.params;
  const auto kCached = params.package_scopes.find(pkg);
  if (kCached != params.package_scopes.end()) return *kCached->second;
  DollarScope& scope = params.cached.emplace_back();
  params.package_scopes.emplace(pkg, &scope);
  NoteItemNamesAt(pkg->items, nullptr, query, depth + 1, scope);
  return scope;
}

const DollarScope& UnitScope(ClassQuery& query, int depth) {
  const DollarParams& params = query.params;
  if (params.unit_scope != nullptr) return *params.unit_scope;
  DollarScope& scope = params.cached.emplace_back();
  params.unit_scope = &scope;
  NoteUnitNamesAt(*params.unit, query, depth + 1, scope);
  return scope;
}

static const InstanceParams& AnyInstance() {
  static const InstanceParams kAny = [] {
    InstanceParams instance;
    instance.values_unknown = true;
    return instance;
  }();
  return kAny;
}

const DollarScope& DesignScope(const ModuleDecl* decl, const DollarScope& outer,
                               ClassQuery& query, int depth) {
  const DollarParams& params = query.params;
  const auto kCached = params.design_scopes.find(decl);
  if (kCached != params.design_scopes.end()) return *kCached->second;
  DollarScope& scope = params.cached.emplace_back();
  params.design_scopes.emplace(decl, &scope);
  scope.outer = &outer;
  NoteModuleParams(decl, AnyInstance(), scope);
  for (const PortDecl& port : decl->ports)
    NoteDeclaredName(port.name, port.data_type, port.unpacked_dims, scope);
  NoteItemNamesAt(decl->items, &AnyInstance(), query, depth + 1, scope);
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
  params.design_scopes.clear();
  return params;
}

static void NoteBlockParam(const ModuleItem* item, DollarScope& scope) {
  scope.typed_vars.erase(item->name);
  NoteTypeItem(item, scope);
  if (!IsTypeParam(item)) {
    NoteParamType(item->name, item->data_type, &item->unpacked_dims,
                  item->init_expr, scope);
  }
}

static void NoteIterators(const Stmt* s, DollarScope& scope) {
  for (size_t k = 0; k < s->foreach_vars.size(); ++k) {
    if (!s->foreach_vars[k].empty())
      scope.iterators.insert_or_assign(s->foreach_vars[k],
                                       DollarIterator{s->expr, k});
  }
}

void NoteLocalNames(const Stmt* s, DollarScope& scope) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    NoteDeclaredName(s->var_name, s->var_decl_type, s->var_unpacked_dims,
                     scope);
    if (s->var_is_param) NoteBlockParam(s->decl_item, scope);
  } else if (s->kind == StmtKind::kBlockItemDecl) {
    NoteTypeItem(s->decl_item, scope);
  } else if (s->kind == StmtKind::kForeach) {
    NoteIterators(s, scope);
  }
  NoteNamedBlock(s, scope);
  ForEachChildStmt(s,
                   [&scope](Stmt* const& sub) { NoteLocalNames(sub, scope); });
}

void NoteModuleParams(const ModuleDecl* decl, const InstanceParams& instance,
                      DollarScope& scope) {
  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [name, value] = decl->params[i];
    NoteInstanceParam(name, instance, scope);
    if (decl->type_param_names.count(name) != 0) continue;
    const bool kKnown =
        decl->localparam_port_names.count(name) != 0 ||
        (!instance.values_unknown && instance.overridden.count(name) == 0);
    NoteParamType(name, decl->param_types[i],
                  PortDims(decl->param_port_unpacked_dims, name),
                  kKnown ? value : nullptr, scope);
  }
}

void NoteSubroutineResult(const ModuleItem* item, DollarScope& scope) {
  if (item->kind != ModuleItemKind::kFunctionDecl ||
      item->return_type.kind == DataTypeKind::kVoid)
    return;
  scope.typed_vars.insert_or_assign(item->name, DollarType{&item->return_type});
}

static void NoteAssertionFormal(const ModuleItem* decl, size_t i,
                                DollarScope& scope) {
  const std::string_view kName = decl->prop_formals[i];
  scope.others.insert(kName);
  const DataType* type = decl->prop_formal_types[i];
  if (type == nullptr) return;
  scope.typed_vars.insert_or_assign(
      kName, DollarType{type, &decl->prop_formal_unpacked_dims[i]});
}

static void NoteAssertionLocals(const std::vector<SeqLocalDecl>& locals,
                                DollarScope& scope) {
  for (const SeqLocalDecl& local : locals) {
    scope.others.insert(local.name);
    scope.typed_vars.insert_or_assign(local.name,
                                      DollarType{&local.named_type});
  }
}

void NoteAssertionFormals(const ModuleItem* decl, DollarScope& scope) {
  for (size_t i = 0; i < decl->prop_formals.size(); ++i)
    NoteAssertionFormal(decl, i, scope);
  NoteAssertionLocals(decl->prop_locals, scope);
  NoteAssertionLocals(decl->seq_linear.locals, scope);
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
