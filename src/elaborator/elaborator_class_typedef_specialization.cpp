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
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

// The types one specialization binds a class's type parameters to, and the
// scope its value parameters' values stand in, the declaring module's names
// with the class's parameters over them.
struct SpecializationBindings {
  std::unordered_map<std::string_view, DataType> types;
  ScopeMap scope;
};

// The argument of `args` binding the class parameter `name`, the `index`th the
// class declares: by name where the specialization names its arguments, as
// §23.10.2.2's form does, and by position otherwise.
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

// A type the specialization's argument names in the declaring module, followed
// through that module's typedefs to the type it stands for, so the class sees
// `logic [7:0]` for the module's `t_t0`. The hop limit keeps a cyclic typedef
// from looping.
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

// The value a value parameter's argument gives it: an expression folded in the
// declaring module's scope, or, where the parser read an argument naming a
// parameter as a type name, that name's value.
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

// Whether the specialization gives an argument at all: a named argument
// written with empty parentheses gives none, and the default stands.
bool GivesArgument(const DataType* arg) {
  return arg != nullptr && (arg->kind != DataTypeKind::kImplicit ||
                            arg->type_ref_expr != nullptr);
}

// The type the `index`th parameter of `cls`, a type parameter, takes: its
// argument, else its default; implicit where it has neither.
DataType TypeParamActual(const ClassDecl* cls, size_t index,
                         const DataType* arg) {
  if (GivesArgument(arg)) return *arg;
  if (index < cls->param_types.size()) return cls->param_types[index];
  return {};
}

// Whether every named argument of `args` names a parameter `cls` declares, and
// no name is given twice. A specialization that breaks either is §23.10.2.2's
// to report, which ResolveParameterizedType does, so it is not bound here.
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

// The bindings `args` make for `cls`'s parameters, each left out taking its
// default; a value default is folded with the parameters before it bound, as
// §6.20.1 lets it name them. Nothing where the named arguments are malformed,
// a value does not fold, or a type parameter has neither an argument nor a
// default.
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

// A dimension bound folded under the specialization, as a literal; null where
// it does not fold.
Expr* FoldedBound(const Expr* bound, const ScopeMap& scope, Arena& arena) {
  auto value = ConstEvalInt(bound, scope);
  return value ? IntLiteral(*value, arena) : nullptr;
}

// Folds every packed dimension of `type` under the specialization. False where
// one does not fold.
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

// The unpacked dimensions `dims` folded under the specialization, each written
// `[left:right]` or `[size]`; nothing where one does not fold, a dynamic,
// queue or associative dimension among them.
std::optional<std::vector<Expr*>> FoldUnpackedDims(
    const std::vector<Expr*>& dims, const ScopeMap& scope, Arena& arena) {
  std::vector<Expr*> folded;
  for (const Expr* dim : dims) {
    if (dim == nullptr) return std::nullopt;
    if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon) {
      Expr* size = FoldedBound(dim, scope, arena);
      if (size == nullptr) return std::nullopt;
      folded.push_back(size);
      continue;
    }
    auto* range = arena.Create<Expr>(*dim);
    range->lhs = FoldedBound(dim->lhs, scope, arena);
    range->rhs = FoldedBound(dim->rhs, scope, arena);
    if (range->lhs == nullptr || range->rhs == nullptr) return std::nullopt;
    folded.push_back(range);
  }
  return folded;
}

// The typedef's type with a type parameter it names replaced by the type the
// specialization binds it to. False where the parameter's name carries a
// packed dimension of its own, which would stack on the actual (§7.4.4), a
// shape this does not carry.
bool SubstituteTypeParam(DataType& type, const SpecializationBindings& bound) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return true;
  auto actual = bound.types.find(type.type_name);
  if (actual == bound.types.end()) return true;
  if (type.packed_dim_left != nullptr) return false;
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

// What a specialization is applied under: the class, what it binds, and the
// arena the folded dimensions are made in.
struct SpecializationCtx {
  const ClassDecl* cls;
  const SpecializationBindings& bound;
  Arena& arena;
};

// The hops a typedef of the class may take through the class's other typedefs,
// `typedef t_vector t_v2;`, before a cyclic chain is given up on.
constexpr int kMaxTypedefHops = 8;

std::optional<SpecializedClassType> SpecializeType(
    const DataType& type, const std::vector<Expr*>& unpacked_dims,
    const SpecializationCtx& ctx, int hops);

// A member's type, whole where the parser kept it, an inline aggregate or
// enumeration, and otherwise rebuilt from the kind, signing, packed dimensions
// and name the member records.
DataType MemberType(const StructMember& m) {
  if (m.nested_type != nullptr) return *m.nested_type;
  DataType type;
  type.kind = m.type_kind;
  type.is_signed = m.is_signed;
  type.packed_dim_left = m.packed_dim_left;
  type.packed_dim_right = m.packed_dim_right;
  type.extra_packed_dims = m.extra_packed_dims;
  type.type_name = m.type_name;
  type.scope_name = m.scope_name;
  return type;
}

// Writes a specialized type back into its member, keeping the whole type for
// an aggregate or enumeration as the parser does for an inline one.
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

// Specializes every member of a structure or union, each in the class's
// parameters as the typedef declaring it is (§6.25). False where one does not
// specialize.
bool SpecializeMembers(DataType& type, const SpecializationCtx& ctx, int hops) {
  for (StructMember& m : type.struct_members) {
    auto spec = SpecializeType(MemberType(m), m.unpacked_dims, ctx, hops);
    if (!spec) return false;
    SetMemberType(m, *spec, ctx.arena);
  }
  return true;
}

// Where `type` names another typedef of the class, that typedef specialized,
// with its unpacked dimensions; `type` itself otherwise. Nothing where the
// name carries packed dimensions of its own, which would stack on the
// typedef's, or the chain of typedefs runs past its hop limit.
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

// `type`, with `unpacked_dims` written on it, specialized: a typedef of the
// class it names followed, a type parameter replaced by its actual, every
// packed and unpacked dimension folded, and a structure's or union's members
// specialized in turn. Nothing where a part does not specialize, or where both
// a typedef's unpacked dimensions and the declaration's own stand, which §7.4.4
// stages one outside the other, a shape this does not carry.
std::optional<SpecializedClassType> SpecializeType(
    const DataType& type, const std::vector<Expr*>& unpacked_dims,
    const SpecializationCtx& ctx, int hops) {
  auto followed = FollowClassTypedef(type, ctx, hops);
  if (!followed) return std::nullopt;
  SpecializedClassType spec = *followed;
  if (!SubstituteTypeParam(spec.type, ctx.bound)) return std::nullopt;
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

// The class a specialization's scope names, with the arguments it is
// specialized by: `C#(bit,4)` names C with its own arguments, and a typedef of
// a specialization, §6.6.7's `typedef Base#(32) MyBaseT;`, names Base with the
// typedef's. A chain of typedefs is followed; the hop limit keeps a cyclic one
// from looping.
std::optional<std::pair<const ClassDecl*, const std::vector<DataType>*>>
SpecializedClass(const DataType& dtype, const CompilationUnit* unit,
                 const TypedefMap& typedefs) {
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
  // §7.4.4 stages a declaration's own dimensions outside the typedef's, a
  // shape this does not carry either.
  if (!spec->unpacked_dims.empty() && !item->unpacked_dims.empty())
    return false;
  item->data_type = spec->type;
  if (!spec->unpacked_dims.empty()) item->unpacked_dims = spec->unpacked_dims;
  return true;
}

}  // namespace delta
