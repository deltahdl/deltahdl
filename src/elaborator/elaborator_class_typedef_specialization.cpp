#include "elaborator/elaborator_class_typedef_specialization.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
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

}  // namespace

bool SpecializeClassScopedTypedef(ModuleItem* item, const CompilationUnit* unit,
                                  const ScopeMap& module_scope,
                                  const TypedefMap& typedefs, Arena& arena) {
  DataType& dtype = item->data_type;
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty())
    return false;
  const ClassDecl* cls = FindClassDecl(dtype.scope_name, unit);
  if (cls == nullptr || cls->params.empty()) return false;
  const ModuleItem* td = ClassTypedefItem(cls, dtype.type_name);
  if (td == nullptr) return false;
  auto bound =
      BindSpecialization(cls, dtype.type_params, module_scope, typedefs);
  if (!bound) return false;
  DataType type = td->typedef_type;
  if (!SubstituteTypeParam(type, *bound)) return false;
  if (!FoldPackedDims(type, bound->scope, arena)) return false;
  auto unpacked = FoldUnpackedDims(td->unpacked_dims, bound->scope, arena);
  if (!unpacked) return false;
  // §7.4.4 stages a declaration's own dimensions outside the typedef's, a
  // shape this does not carry either.
  if (!unpacked->empty() && !item->unpacked_dims.empty()) return false;
  type.is_const = dtype.is_const;
  dtype = type;
  if (!unpacked->empty()) item->unpacked_dims = *unpacked;
  return true;
}

}  // namespace delta
