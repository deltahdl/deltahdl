#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/net_or_variable_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/scope_value_type.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_scope_prefix.h"
#include "elaborator/type_site_lookup.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static const RtlirParamDecl* ValueParamNamed(const RtlirModule* mod,
                                             std::string_view name) {
  for (const auto& p : mod->params) {
    if (p.name == name && !p.is_type_param) return &p;
  }
  return nullptr;
}

static std::optional<ValueShape> NamedValueShape(std::string_view name,
                                                 const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return ValueShape{v.width, v.is_signed};
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return ValueShape{n.width, n.is_signed};
  }
  if (const RtlirParamDecl* pd = ValueParamNamed(mod, name)) {
    ParamStorageShape shape = ParamStorageShapeOf(*pd);
    return ValueShape{shape.width, shape.is_signed};
  }
  return std::nullopt;
}

static ValueShapeOf ShapesIn(const RtlirModule* mod) {
  return [mod](std::string_view name) { return NamedValueShape(name, mod); };
}

void AdoptExpressionType(DataType& dt, const std::optional<DataType>& type,
                         Arena& arena) {
  if (!type) {
    AdoptLogicVector(dt, {}, arena);
    return;
  }
  if (type->struct_members.empty() && type->enum_members.empty()) {
    AdoptReferencedType(dt, *type);
    return;
  }
  bool is_const = dt.is_const;
  dt = *type;
  dt.is_const = is_const;
  dt.type_ref_expr = nullptr;
}

static std::optional<DataType> ModuleValueType(std::string_view name,
                                               const TypeRefScope& scope) {
  const auto& ports = scope.decl->ports;
  auto port = std::ranges::find(ports, name, &PortDecl::name);
  if (port != ports.end()) return port->data_type;
  const ModuleItem* item = ItemNamed(scope.decl->items, name);
  if (item == nullptr) return std::nullopt;
  return DeclaredValueType(*item, ShapesIn(scope.mod), scope.arena);
}

static const RtlirEnumMember* EnumConstantNamed(const RtlirModule* mod,
                                                std::string_view name,
                                                std::string_view& key) {
  for (const auto& [enum_key, members] : mod->enum_types) {
    auto it = std::ranges::find(members, name, &RtlirEnumMember::name);
    if (it == members.end()) continue;
    key = enum_key;
    return &*it;
  }
  return nullptr;
}

static std::string_view AdoptEnumerationType(DataType& dt,
                                             const RtlirEnumMember& constant,
                                             std::string_view key,
                                             const TypeRefScope& scope) {
  if (scope.typedefs.count(key) != 0) {
    AdoptReferencedType(dt, TypeNameToDataType(key));
    return {};
  }
  bool is_const = dt.is_const;
  dt = *constant.enumeration;
  dt.is_const = is_const;
  return key;
}

static void ResolveMemberTypeRefs(
    DataType& dt, Arena& arena, const std::function<void(DataType&)>& resolve) {
  for (StructMember& m : dt.struct_members) {
    if (m.nested_type == nullptr || m.nested_type->type_ref_expr == nullptr) {
      continue;
    }
    DataType type = *m.nested_type;
    resolve(type);
    m.type_kind = type.kind;
    m.is_signed = type.is_signed;
    m.packed_dim_left = type.packed_dim_left;
    m.packed_dim_right = type.packed_dim_right;
    m.extra_packed_dims = type.extra_packed_dims;
    m.type_name = type.type_name;
    m.scope_name = type.scope_name;
    m.nested_type = arena.Create<DataType>(type);
  }
}

static bool ResolveScopedTypeRef(DataType& dt, const Expr* ref,
                                 const TypeRefScope& scope) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution) {
    return false;
  }
  if (ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (ref->rhs == nullptr || ref->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view prefix = ref->lhs->text;
  if (const DataType* resolved =
          FindClassScopedTypedefType(prefix, ref->rhs->text, scope.unit)) {
    AdoptReferencedType(dt, *resolved);
    return true;
  }
  if (const DataType* bound =
          TypeRefThroughBoundPrefix(prefix, ref->rhs->text, scope.typedefs)) {
    AdoptReferencedType(dt, *bound);
    return true;
  }
  const PackageDecl* pkg = PackageDeclaring(
      scope.unit, ref->rhs->text,
      [&](std::string_view package) { return package == prefix; });
  if (pkg == nullptr) return false;
  AdoptReferencedType(dt, ScopeValueType(*ItemNamed(pkg->items, ref->rhs->text),
                                         pkg->items, scope.arena));
  return true;
}

static void ResolveNamedTypeRef(DataType& dt, std::string_view name,
                                const TypeRefScope& scope) {
  if (const RtlirParamDecl* pd = ValueParamNamed(scope.mod, name)) {
    if (pd->decl_type != nullptr && !pd->decl_type_implicit) {
      AdoptReferencedType(dt, *pd->decl_type);
      return;
    }
    ParamStorageShape shape = ParamStorageShapeOf(*pd);
    AdoptLogicVector(dt, {shape.width, shape.is_signed}, scope.arena);
    return;
  }
  DataType spelled = TypeNameToDataType(name);
  if (spelled.kind != DataTypeKind::kNamed || scope.typedefs.count(name) != 0) {
    AdoptReferencedType(dt, spelled);
    return;
  }
  if (std::optional<DataType> own = ModuleValueType(name, scope)) {
    AdoptReferencedType(dt, *own);
    return;
  }
  if (std::optional<DataType> outer = OuterValueType(name, scope)) {
    AdoptReferencedType(dt, *outer);
  }
}

static bool AdoptRecordedValueType(
    DataType& dt, std::string_view name, const RtlirModule& mod,
    std::unordered_map<std::string_view, DataTypeKind>& var_types,
    Arena& arena) {
  for (const auto& v : mod.variables) {
    if (v.name != name) continue;
    dt.kind = var_types[name];
    dt.is_signed = v.is_signed;
    if (dt.kind == DataTypeKind::kLogic || dt.kind == DataTypeKind::kBit ||
        dt.kind == DataTypeKind::kReg) {
      SetTypeRefPackedDims(dt, v.width, arena);
    }
    dt.type_ref_expr = nullptr;
    return true;
  }
  for (const auto& n : mod.nets) {
    if (n.name != name) continue;
    AdoptLogicVector(dt, {n.width, n.is_signed}, arena);
    return true;
  }
  auto it = var_types.find(name);
  if (it == var_types.end()) return false;
  dt.kind = it->second;
  dt.type_ref_expr = nullptr;
  return true;
}

std::string_view Elaborator::ResolveTypeRef(DataType& dt, SourceLoc loc,
                                            const RtlirModule* mod) {
  ResolveMemberTypeRefs(
      dt, arena_, [&](DataType& type) { ResolveTypeRef(type, loc, mod); });
  if (!dt.type_ref_expr) return {};
  auto* ref = dt.type_ref_expr;
  CheckTypeRefArgInner(ref, loc, mod);
  const ModuleDecl* decl = module_decl_path_.back();
  const TypeRefScope kScope{mod, typedefs_, unit_, loc, arena_, decl};
  ReportTypeRefPrefixNotAClass(ref, loc, {mod->params, typedefs_, class_names_},
                               diag_);
  if (ResolveScopedTypeRef(dt, ref, kScope)) return {};
  if (std::optional<UnpackedArrayType> array = TypeRefValueArray(ref, mod)) {
    AdoptReferencedType(dt, array->element);
    return {};
  }
  if (std::optional<DataType> returned = CalledFunctionType(ref)) {
    AdoptReferencedType(dt, *returned);
    return {};
  }
  if (!ref->scope_prefix.empty()) {
    if (std::optional<DataType> scoped = TypeRefExprType(ref, mod)) {
      AdoptExpressionType(dt, scoped, arena_);
      return {};
    }
  }
  if (ref->kind != ExprKind::kIdentifier) {
    AdoptExpressionType(dt, TypeRefExprType(ref, mod), arena_);
    return {};
  }
  std::string_view enumeration;
  if (const RtlirEnumMember* constant =
          EnumConstantNamed(mod, ref->text, enumeration)) {
    return AdoptEnumerationType(dt, *constant, enumeration, kScope);
  }
  if (std::optional<DataType> declared = NetOrVariableType(
          *mod,
          DeclaredScopedName(ref->text, gen_prefix_scopes_, declared_names_))) {
    AdoptReferencedType(dt, *declared);
    return {};
  }
  if (AdoptRecordedValueType(dt, ref->text, *mod, var_types_, arena_)) {
    return {};
  }
  ResolveNamedTypeRef(dt, ref->text, kScope);
  return {};
}

void ResolveScopeTypeRef(DataType& dt, const std::vector<ModuleItem*>& items,
                         Arena& arena) {
  const Expr* ref = dt.type_ref_expr;
  if (ref == nullptr || ref->kind != ExprKind::kIdentifier) return;
  DataType spelled = TypeNameToDataType(ref->text);
  const ModuleItem* item = ItemNamed(items, ref->text);
  if (spelled.kind != DataTypeKind::kNamed ||
      (item != nullptr && item->kind == ModuleItemKind::kTypedef)) {
    AdoptReferencedType(dt, spelled);
    return;
  }
  if (item == nullptr) return;
  AdoptReferencedType(dt, ScopeValueType(*item, items, arena));
}

static const ClassDecl* FindClassAmong(std::string_view name,
                                       const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr && item->class_decl->name == name) {
      return item->class_decl;
    }
  }
  return nullptr;
}

static void TakeUniqueMatch(const ClassDecl* found, const ClassDecl*& only,
                            bool& ambiguous) {
  if (found == nullptr) return;
  if (only != nullptr) ambiguous = true;
  only = found;
}

const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  const ClassDecl* only = nullptr;
  bool ambiguous = false;
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      TakeUniqueMatch(FindClassAmong(name, decl->items), only, ambiguous);
    }
  }
  for (const auto* pkg : unit->packages) {
    TakeUniqueMatch(FindClassAmong(name, pkg->items), only, ambiguous);
  }
  return ambiguous ? nullptr : only;
}

static void TakeDeclaringSite(const ClassDecl* cls,
                              const std::vector<ModuleItem*>& items,
                              SiteKind kind, TypeSite& found) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl == cls) {
      found = TypeSite{&items, items.size(), kind};
    }
  }
}

const ClassDecl* FindBaseClass(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  const ClassDecl* in_package =
      FindClassInPackage(cls->base_class_scope, cls->base_class, unit);
  if (in_package != nullptr) return in_package;
  TypeSite site;
  TakeDeclaringSite(cls, unit->cu_items, SiteKind::kUnit, site);
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      TakeDeclaringSite(cls, decl->items, SiteKind::kModule, site);
    }
  }
  for (const auto* pkg : unit->packages) {
    TakeDeclaringSite(cls, pkg->items, SiteKind::kPackage, site);
  }
  const ClassDecl* seen =
      site.items == nullptr ? nullptr : ClassIn(*unit, site, cls->base_class);
  return seen != nullptr ? seen : FindClassDecl(cls->base_class, unit);
}

static void AppendClassAndNested(const ClassDecl* cls,
                                 std::vector<const ClassDecl*>& out) {
  out.push_back(cls);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class != nullptr)
      AppendClassAndNested(m->nested_class, out);
  }
}

static void AppendClassDecls(const std::vector<ModuleItem*>& items,
                             std::vector<const ClassDecl*>& out);

static void AppendGenerateClassDecls(const ModuleItem* item,
                                     std::vector<const ClassDecl*>& out) {
  for (; item != nullptr; item = item->gen_else) {
    AppendClassDecls(item->gen_body, out);
    for (const auto& case_item : item->gen_case_items) {
      AppendClassDecls(case_item.body, out);
    }
  }
}

static void AppendClassDecls(const std::vector<ModuleItem*>& items,
                             std::vector<const ClassDecl*>& out) {
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      AppendClassAndNested(item->class_decl, out);
    }
    AppendGenerateClassDecls(item, out);
  }
}

std::vector<const ClassDecl*> AllClassDecls(const CompilationUnit* unit) {
  std::vector<const ClassDecl*> out;
  for (const auto* cls : unit->classes) AppendClassAndNested(cls, out);
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) AppendClassDecls(decl->items, out);
  }
  for (const auto* pkg : unit->packages) AppendClassDecls(pkg->items, out);
  return out;
}

std::string_view NestedClassKey(const DataType& dtype,
                                const CompilationUnit* unit, Arena& arena) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return {};
  const ClassDecl* outer = FindClassDecl(dtype.scope_name, unit);
  if (outer == nullptr) return {};
  for (const auto* m : outer->members) {
    if (m->kind != ClassMemberKind::kClassDecl || m->name != dtype.type_name)
      continue;
    return *arena.Create<std::string>(std::string(dtype.scope_name) +
                                      "::" + std::string(dtype.type_name));
  }
  return {};
}

std::string_view PackageClassKey(const DataType& dtype,
                                 const TypedefMap& typedefs,
                                 const CompilationUnit* unit, Arena& arena) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return {};
  DataType end = LastTypeInChain(dtype, typedefs);
  if (end.scope_name.empty()) end.scope_name = dtype.scope_name;
  for (const auto* pkg : unit->packages) {
    if (pkg->name != end.scope_name) continue;
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl ||
          item->class_decl->name != end.type_name)
        continue;
      return *arena.Create<std::string>(std::string(end.scope_name) +
                                        "::" + std::string(end.type_name));
    }
  }
  return {};
}

static const ModuleItem* FindClassTypedef(const ClassDecl* cls,
                                          std::string_view member_name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == member_name) {
      return m->typedef_item;
    }
  }
  return nullptr;
}

const ModuleItem* FindClassScopedTypedefItem(std::string_view cls_name,
                                             std::string_view type_name,
                                             const CompilationUnit* unit) {
  const auto* cls = FindClassDecl(cls_name, unit);
  if (cls == nullptr) return nullptr;
  return FindClassTypedef(cls, type_name);
}

const DataType* FindClassScopedTypedefType(std::string_view cls_name,
                                           std::string_view type_name,
                                           const CompilationUnit* unit) {
  const ModuleItem* td = FindClassScopedTypedefItem(cls_name, type_name, unit);
  if (td == nullptr) return nullptr;
  return &td->typedef_type;
}

bool ResolveClassScopedDeclType(DataType& dtype, const TypedefMap& typedefs,
                                const CompilationUnit* unit) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) {
    return false;
  }
  if (typedefs.count(TypeChainKey(dtype)) > 0) return false;
  const ClassDecl* cls = ClassOfChainedScope(dtype, unit);
  if (cls == nullptr) return false;
  const ModuleItem* td = FindClassTypedef(cls, dtype.type_name);
  if (td == nullptr) return false;
  const DataType& resolved = td->typedef_type;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.type_name = resolved.type_name;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  return true;
}

static bool ClassDeclaresMember(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->name == name) return true;
  }
  return false;
}

void ReportUnresolvedClassScopedType(const DataType& dtype, SourceLoc loc,
                                     const TypedefMap& typedefs,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return;
  if (!dtype.type_params.empty()) return;
  if (typedefs.count(TypeChainKey(dtype)) > 0) return;
  const ClassDecl* cls = ClassOfChainedScope(dtype, unit);
  if (cls == nullptr) return;
  if (!cls->base_class.empty() || !cls->extends_interfaces.empty()) return;
  if (cls->members.empty()) return;
  if (ClassDeclaresMember(cls, dtype.type_name)) return;
  diag.Error(loc,
             std::format("class '{}' declares no type '{}'", dtype.scope_name,
                         dtype.type_name),
             Subclause("8.23"));
}

static std::unordered_map<std::string_view, const DataType*>
BuildSpecializationSubst(const ClassDecl* cls,
                         const std::vector<DataType>& args) {
  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < args.size(); ++i) {
    if (!args[i].param_arg_name.empty()) {
      subst[args[i].param_arg_name] = &args[i];
    } else if (i < cls->params.size()) {
      subst[cls->params[i].first] = &args[i];
    }
  }
  size_t defaults = std::min(cls->params.size(), cls->param_types.size());
  for (size_t i = 0; i < defaults; ++i) {
    if (cls->param_types[i].kind == DataTypeKind::kImplicit) continue;
    subst.emplace(cls->params[i].first, &cls->param_types[i]);
  }
  return subst;
}

static void ValidateSpecializationArgNames(const ClassDecl* cls,
                                           const std::vector<DataType>& args,
                                           DiagEngine& diag, SourceLoc loc) {
  std::unordered_set<std::string_view> declared;
  for (const auto& [pname, pexpr] : cls->params) declared.insert(pname);
  std::unordered_set<std::string_view> assigned;
  for (const auto& arg : args) {
    if (arg.param_arg_name.empty()) continue;
    if (declared.count(arg.param_arg_name) == 0) {
      diag.Error(loc,
                 std::format("class '{}' has no parameter '{}'", cls->name,
                             arg.param_arg_name),
                 Subclause("23.10.2.2"));
    } else if (!assigned.insert(arg.param_arg_name).second) {
      diag.Error(loc,
                 std::format("parameter '{}' of class '{}' is assigned more "
                             "than once",
                             arg.param_arg_name, cls->name),
                 Subclause("23.10.2.2"));
    }
  }
}

bool ResolveParameterizedType(DataType& dtype, const CompilationUnit* unit,
                              DiagEngine& diag, SourceLoc loc) {
  if (dtype.scope_name.empty() || dtype.type_params.empty()) return false;
  const auto* cls = FindClassDecl(dtype.scope_name, unit);
  if (!cls) return false;
  ValidateSpecializationArgNames(cls, dtype.type_params, diag, loc);
  auto subst = BuildSpecializationSubst(cls, dtype.type_params);

  std::string_view param_name = dtype.type_name;
  if (!subst.count(param_name)) {
    const auto* td = FindClassTypedef(cls, dtype.type_name);
    if (!td) return false;
    param_name = td->typedef_type.type_name;
  }
  auto it = subst.find(param_name);
  if (it == subst.end()) return false;
  const DataType& resolved = *it->second;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  dtype.type_name = resolved.type_name;
  dtype.scope_name = {};
  dtype.type_params.clear();
  return true;
}

}  // namespace delta
