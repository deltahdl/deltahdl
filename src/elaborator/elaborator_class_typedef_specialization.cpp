#include "elaborator/elaborator_class_typedef_specialization.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "elaborator/unpacked_array_type.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

struct SpecializationBindings {
  std::unordered_map<std::string_view, DataType> types;
  ScopeMap scope;
  std::unordered_set<std::string_view> given;
};

const DataType* ArgumentFor(const std::vector<DataType>& args, size_t index,
                            std::string_view name) {
  bool named = std::any_of(args.begin(), args.end(), [](const DataType& a) {
    return !a.param_arg_name.empty();
  });
  if (!named) return index < args.size() ? &args[index] : nullptr;
  for (const DataType& a : args) {
    if (a.param_arg_name == name) return &a;
  }
  return nullptr;
}

DataType InDeclaringModule(DataType type, const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && type.kind == DataTypeKind::kNamed &&
                     type.scope_name.empty() && type.packed_dim_left == nullptr;
       ++hops) {
    auto it = typedefs.find(type.type_name);
    if (it == typedefs.end()) break;
    type = it->second;
  }
  return type;
}

std::optional<int64_t> ArgumentValue(const DataType& arg,
                                     const ScopeMap& module_scope) {
  if (arg.type_ref_expr != nullptr)
    return ConstEvalInt(arg.type_ref_expr, module_scope);
  if (arg.kind == DataTypeKind::kNamed && arg.scope_name.empty()) {
    auto it = module_scope.find(arg.type_name);
    if (it != module_scope.end()) return it->second;
  }
  return std::nullopt;
}

bool GivesArgument(const DataType* arg) {
  return arg != nullptr && (arg->kind != DataTypeKind::kImplicit ||
                            arg->type_ref_expr != nullptr);
}

DataType TypeParamActual(const ClassDecl* cls, size_t index,
                         const DataType* arg) {
  if (GivesArgument(arg)) return *arg;
  if (index < cls->param_types.size()) return cls->param_types[index];
  return {};
}

bool NamesWellFormed(const ClassDecl* cls, const std::vector<DataType>& args) {
  std::unordered_set<std::string_view> assigned;
  for (const DataType& a : args) {
    if (a.param_arg_name.empty()) continue;
    bool declared = std::any_of(
        cls->params.begin(), cls->params.end(),
        [&a](const auto& param) { return param.first == a.param_arg_name; });
    if (!declared || !assigned.insert(a.param_arg_name).second) return false;
  }
  return true;
}

std::optional<SpecializationBindings> BindSpecialization(
    const ClassDecl* cls, const std::vector<DataType>& args,
    const ScopeMap& module_scope, const TypedefMap& typedefs) {
  if (!NamesWellFormed(cls, args)) return std::nullopt;
  SpecializationBindings bound;
  bound.scope = module_scope;
  for (size_t i = 0; i < cls->params.size(); ++i) {
    const auto& [name, default_value] = cls->params[i];
    const DataType* arg = ArgumentFor(args, i, name);
    if (cls->type_param_names.count(name) != 0) {
      DataType type = TypeParamActual(cls, i, arg);
      if (type.kind == DataTypeKind::kImplicit) return std::nullopt;
      bound.types[name] = InDeclaringModule(type, typedefs);
      if (GivesArgument(arg)) bound.given.insert(name);
      continue;
    }
    std::optional<int64_t> value =
        GivesArgument(arg) ? ArgumentValue(*arg, module_scope)
                           : ConstEvalInt(default_value, bound.scope);
    if (!value) return std::nullopt;
    bound.scope[name] = *value;
  }
  return bound;
}

Expr* IntLiteral(int64_t value, Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = value;
  return e;
}

Expr* FoldedBound(const Expr* bound, const ScopeMap& scope, Arena& arena) {
  auto value = ConstEvalInt(bound, scope);
  return value ? IntLiteral(*value, arena) : nullptr;
}

bool FoldPackedDims(DataType& type, const ScopeMap& scope, Arena& arena) {
  if (type.packed_dim_left != nullptr) {
    type.packed_dim_left = FoldedBound(type.packed_dim_left, scope, arena);
    type.packed_dim_right = FoldedBound(type.packed_dim_right, scope, arena);
    if (type.packed_dim_left == nullptr || type.packed_dim_right == nullptr)
      return false;
  }
  for (auto& [left, right] : type.extra_packed_dims) {
    left = FoldedBound(left, scope, arena);
    right = FoldedBound(right, scope, arena);
    if (left == nullptr || right == nullptr) return false;
  }
  return true;
}

bool IsAssociativeDim(const Expr* dim) {
  return (dim->kind == ExprKind::kIdentifier && dim->text == "*") ||
         IndexDimType(dim).has_value();
}

std::optional<Expr*> FoldedUnpackedDim(Expr* dim, const ScopeMap& scope,
                                       Arena& arena) {
  if (dim == nullptr || IsQueueDim(dim)) return dim;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto* range = arena.Create<Expr>(*dim);
    range->lhs = FoldedBound(dim->lhs, scope, arena);
    range->rhs = FoldedBound(dim->rhs, scope, arena);
    if (range->lhs == nullptr || range->rhs == nullptr) return std::nullopt;
    return range;
  }
  Expr* size = FoldedBound(dim, scope, arena);
  if (size == nullptr && !IsAssociativeDim(dim)) return std::nullopt;
  return size != nullptr ? size : dim;
}

std::optional<std::vector<Expr*>> FoldUnpackedDims(
    const std::vector<Expr*>& dims, const ScopeMap& scope, Arena& arena) {
  std::vector<Expr*> folded;
  for (Expr* dim : dims) {
    std::optional<Expr*> one = FoldedUnpackedDim(dim, scope, arena);
    if (!one) return std::nullopt;
    folded.push_back(*one);
  }
  return folded;
}

bool SubstituteTypeParam(SpecializedClassType& spec,
                         const SpecializationBindings& bound) {
  DataType& type = spec.type;
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return true;
  auto actual = bound.types.find(type.type_name);
  if (actual == bound.types.end()) return true;
  if (type.packed_dim_left != nullptr) return false;
  spec.names_argument = bound.given.count(actual->first) != 0;
  type = actual->second;
  return true;
}

const ModuleItem* ClassTypedefItem(const ClassDecl* cls,
                                   std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == name)
      return m->typedef_item;
  }
  return nullptr;
}

struct SpecializationCtx {
  const ClassDecl* cls;
  const SpecializationBindings& bound;
  Arena& arena;
};

constexpr int kMaxTypedefHops = 8;

std::optional<SpecializedClassType> SpecializeType(
    const DataType& type, const std::vector<Expr*>& unpacked_dims,
    const SpecializationCtx& ctx, int hops);

void SetMemberType(StructMember& m, const SpecializedClassType& spec,
                   Arena& arena) {
  const DataType& type = spec.type;
  m.type_kind = type.kind;
  m.is_signed = type.is_signed;
  m.packed_dim_left = type.packed_dim_left;
  m.packed_dim_right = type.packed_dim_right;
  m.extra_packed_dims = type.extra_packed_dims;
  m.type_name = type.type_name;
  m.scope_name = type.scope_name;
  bool whole = type.kind == DataTypeKind::kStruct ||
               type.kind == DataTypeKind::kUnion ||
               type.kind == DataTypeKind::kEnum;
  m.nested_type = whole ? arena.Create<DataType>(type) : nullptr;
  m.resolved_width = 0;
  m.unpacked_dims = spec.unpacked_dims;
}

bool SpecializeMembers(DataType& type, const SpecializationCtx& ctx, int hops) {
  for (StructMember& m : type.struct_members) {
    auto spec =
        SpecializeType(MemberWrittenType(m), m.unpacked_dims, ctx, hops);
    if (!spec) return false;
    SetMemberType(m, *spec, ctx.arena);
  }
  return true;
}

std::optional<SpecializedClassType> FollowClassTypedef(
    const DataType& type, const SpecializationCtx& ctx, int hops) {
  bool names_typedef = type.kind == DataTypeKind::kNamed &&
                       type.scope_name.empty() &&
                       ctx.bound.types.count(type.type_name) == 0;
  const ModuleItem* td =
      names_typedef ? ClassTypedefItem(ctx.cls, type.type_name) : nullptr;
  if (td == nullptr) return SpecializedClassType{type, {}};
  if (type.packed_dim_left != nullptr || hops >= kMaxTypedefHops)
    return std::nullopt;
  return SpecializeType(td->typedef_type, td->unpacked_dims, ctx, hops + 1);
}

std::optional<SpecializedClassType> SpecializeType(
    const DataType& type, const std::vector<Expr*>& unpacked_dims,
    const SpecializationCtx& ctx, int hops) {
  auto followed = FollowClassTypedef(type, ctx, hops);
  if (!followed) return std::nullopt;
  SpecializedClassType spec = *followed;
  if (!SubstituteTypeParam(spec, ctx.bound)) return std::nullopt;
  if (!FoldPackedDims(spec.type, ctx.bound.scope, ctx.arena))
    return std::nullopt;
  if (!SpecializeMembers(spec.type, ctx, hops)) return std::nullopt;
  auto own = FoldUnpackedDims(unpacked_dims, ctx.bound.scope, ctx.arena);
  if (!own) return std::nullopt;
  if (own->empty()) return spec;
  if (!spec.unpacked_dims.empty()) return std::nullopt;
  spec.unpacked_dims = *own;
  return spec;
}

std::optional<std::pair<const ClassDecl*, const std::vector<DataType>*>>
SpecializedClass(const DataType& dtype, const CompilationUnit* unit,
                 const TypedefMap& typedefs) {
  if (!OuterScopePrefixes(dtype).empty()) {
    const ClassDecl* cls = ClassOfChainedScope(dtype, unit);
    if (cls == nullptr) return std::nullopt;
    return std::make_pair(cls, &dtype.type_params);
  }
  std::string_view scope = dtype.scope_name;
  const std::vector<DataType>* args = &dtype.type_params;
  for (int hops = 0; hops < kMaxTypedefHops; ++hops) {
    if (const ClassDecl* cls = FindClassDecl(scope, unit))
      return std::make_pair(cls, args);
    auto td = typedefs.find(scope);
    if (td == typedefs.end() || td->second.kind != DataTypeKind::kNamed ||
        !td->second.scope_name.empty() || !args->empty())
      return std::nullopt;
    scope = td->second.type_name;
    args = &td->second.type_params;
  }
  return std::nullopt;
}

}  // namespace

std::optional<SpecializedClassType> SpecializeClassScopedType(
    const DataType& dtype, const CompilationUnit* unit,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty())
    return std::nullopt;
  auto specialized = SpecializedClass(dtype, unit, typedefs);
  if (!specialized) return std::nullopt;
  const auto [cls, args] = *specialized;
  if (cls->params.empty()) return std::nullopt;
  const ModuleItem* td = ClassTypedefItem(cls, dtype.type_name);
  if (td == nullptr) return std::nullopt;
  auto bound = BindSpecialization(cls, *args, module_scope, typedefs);
  if (!bound) return std::nullopt;
  auto spec = SpecializeType(td->typedef_type, td->unpacked_dims,
                             {cls, *bound, arena}, 0);
  if (spec) spec->type.is_const = dtype.is_const;
  return spec;
}

bool SpecializeClassScopedTypedef(ModuleItem* item, const CompilationUnit* unit,
                                  const ScopeMap& module_scope,
                                  const TypedefMap& typedefs, Arena& arena) {
  auto spec = SpecializeClassScopedType(item->data_type, unit, module_scope,
                                        typedefs, arena);
  if (!spec) return false;
  if (!spec->unpacked_dims.empty() && !item->unpacked_dims.empty())
    return false;
  item->data_type = spec->type;
  if (!spec->unpacked_dims.empty()) item->unpacked_dims = spec->unpacked_dims;
  return true;
}

void ResolveClassScopedFormalTypes(ModuleItem& item,
                                   const CompilationUnit* unit,
                                   const ScopeMap& module_scope,
                                   const TypedefMap& typedefs, Arena& arena) {
  for (size_t i = 0; i < item.prop_formal_types.size(); ++i) {
    DataType* type = item.prop_formal_types[i];
    if (type == nullptr || type->scope_name.empty()) continue;
    std::optional<SpecializedClassType> spec =
        SpecializeClassScopedType(*type, unit, module_scope, typedefs, arena);
    if (spec.has_value()) {
      *type = spec->type;
      item.prop_formal_unpacked_dims[i] = spec->unpacked_dims;
      continue;
    }
    const ModuleItem* declared =
        FindClassScopedTypedefItem(type->scope_name, type->type_name, unit);
    if (declared == nullptr) continue;
    *type = declared->typedef_type;
    item.prop_formal_unpacked_dims[i] = declared->unpacked_dims;
  }
}

std::optional<bool> SameSpecialization(const ClassSpecialization& a,
                                       const ClassSpecialization& b,
                                       const ScopeMap& module_scope,
                                       const TypedefMap& typedefs) {
  if (a.cls != b.cls) return false;
  auto bound_a = BindSpecialization(a.cls, *a.args, module_scope, typedefs);
  auto bound_b = BindSpecialization(b.cls, *b.args, module_scope, typedefs);
  if (!bound_a || !bound_b) return std::nullopt;
  return std::ranges::all_of(a.cls->params, [&](const auto& param) {
    const std::string_view kName = param.first;
    if (a.cls->type_param_names.count(kName) != 0)
      return TypesMatch(bound_a->types[kName], bound_b->types[kName]);
    return bound_a->scope[kName] == bound_b->scope[kName];
  });
}

std::optional<SpecializedClassType> SpecializedMemberType(
    const ClassSpecialization& handle, const SpecializedClassType& written,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena) {
  auto bound =
      BindSpecialization(handle.cls, *handle.args, module_scope, typedefs);
  if (!bound) return std::nullopt;
  return SpecializeType(written.type, written.unpacked_dims,
                        {handle.cls, *bound, arena}, 0);
}

static std::optional<DataType> ExtendsArgument(
    const DataType& written, const ClassDecl* cls,
    const SpecializationBindings& bound, Arena& arena) {
  if (written.type_ref_expr != nullptr) {
    std::optional<int64_t> value = ArgumentValue(written, bound.scope);
    if (!value) return std::nullopt;
    DataType arg;
    arg.type_ref_expr = IntLiteral(*value, arena);
    arg.param_arg_name = written.param_arg_name;
    return arg;
  }
  std::optional<SpecializedClassType> type =
      SpecializeType(written, {}, {cls, bound, arena}, 0);
  if (!type) return std::nullopt;
  type->type.param_arg_name = written.param_arg_name;
  return std::move(type->type);
}

const std::vector<DataType>* SpecializedExtendsArguments(
    const ClassSpecialization& handle, const ScopeMap& module_scope,
    const TypedefMap& typedefs, Arena& arena) {
  if (handle.cls->params.empty()) return &handle.cls->base_class_type_params;
  auto bound =
      BindSpecialization(handle.cls, *handle.args, module_scope, typedefs);
  if (!bound) return nullptr;
  auto* args = arena.Create<std::vector<DataType>>();
  for (const DataType& written : handle.cls->base_class_type_params) {
    std::optional<DataType> arg =
        ExtendsArgument(written, handle.cls, *bound, arena);
    if (!arg) return nullptr;
    args->push_back(std::move(*arg));
  }
  return args;
}

}  // namespace delta
