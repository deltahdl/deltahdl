// §20.6.1 (printed pages 628-629 of IEEE 1800-2023): $typename during the
// run, written by the clause's steps (elaborator/typename_writer.h) from the
// running design: a variable, a property or a type parameter of the object a
// method runs on, a typedef name, a type node, a built-in type keyword, or an
// expression's self-determined type.

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/typename_writer.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// Step a: the type the typedef name `type_name`, written behind the scope
// `scope_name` where it was, stands for in the running design, null where no
// typedef declares it; `prefix` is set to the scope a package's typedef made
// visible by an import is named behind.
const DataType* DeclaredTypeOfName(SimContext& ctx, std::string_view scope_name,
                                   std::string_view type_name,
                                   std::string& prefix) {
  std::string key = scope_name.empty() ? std::string(type_name)
                                       : std::string(scope_name) +
                                             "::" + std::string(type_name);
  const DataType* named = ctx.FindTypeDeclaration(key);
  if (named != nullptr || !scope_name.empty()) return named;
  // §26.3: a name a package declares, made visible by an import.
  std::string_view imported = ctx.FindPackageTypedefKey(type_name);
  if (imported.empty()) return nullptr;
  prefix = std::string(imported.substr(0, imported.size() - type_name.size()));
  return ctx.FindTypeDeclaration(imported);
}

// What the §20.6.1 steps ask of the place a type is written in, answered from
// the running design.
TypenameEnvironment SimTypenameEnvironment(SimContext& ctx, Arena& arena) {
  TypenameEnvironment env;
  env.value_of = [&ctx, &arena](const Expr* expr) {
    return static_cast<int64_t>(EvalExpr(expr, ctx, arena).ToUint64());
  };
  env.resolve_name = [&ctx](std::string_view scope_name,
                            std::string_view type_name, std::string& prefix) {
    return DeclaredTypeOfName(ctx, scope_name, type_name, prefix);
  };
  env.qualified_class_name = [&ctx](std::string_view scope_name,
                                    std::string_view type_name) {
    const ClassTypeInfo* cls =
        scope_name.empty() ? ctx.FindClassType(type_name) : nullptr;
    if (cls == nullptr || cls->package.empty()) return std::string();
    return std::string(cls->package) + "::" + std::string(cls->name);
  };
  env.scope_name = [&ctx]() -> std::string_view {
    return ctx.CurrentScopeName();
  };
  env.width_of = [&ctx](const DataType& type) {
    return DeclaredTypeWidth(type, ctx);
  };
  env.name_self_type = [&ctx](std::string_view name) -> SelfType {
    const Variable* var = ctx.FindVariable(name);
    if (var == nullptr || var->is_real || var->is_string ||
        !var->declared_unpacked.empty()) {
      return {};
    }
    return {var->value.width, var->is_signed, var->is_4state, true};
  };
  env.is_real = [&ctx](const Expr* expr) { return SimSelfReal(expr, ctx); };
  return env;
}

// The declaration of the property `name` of the object's class or a class it
// derives from, null where none declares it.
const ClassMember* PropertyDeclaration(const ClassTypeInfo* type,
                                       std::string_view name) {
  for (; type != nullptr; type = type->parent) {
    if (type->decl == nullptr) continue;
    for (const ClassMember* member : type->decl->members) {
      if (member->kind == ClassMemberKind::kProperty && member->name == name) {
        return member;
      }
    }
  }
  return nullptr;
}

// A variable as $typename writes it: by the type its declaration recorded,
// or else by the kind the variable alone says it is; empty where neither
// says.
std::string TypenameOfVariable(const Variable& var, std::string_view name,
                               TypenameWriter& writer) {
  std::string unpacked(var.declared_unpacked);
  if (var.declared_type != nullptr) {
    return writer.OfType(*var.declared_type, var.declared_scope, name) +
           unpacked;
  }
  if (var.is_string) return "string" + unpacked;
  if (var.is_real) return "real" + unpacked;
  return {};
}

// What an identifier argument names, as $typename writes it: a variable, a
// property or a type parameter of the object a method runs on, a typedef
// name, or a built-in type keyword; empty where it names none of them.
std::string TypenameOfIdentifier(std::string_view name, TypenameWriter& writer,
                                 SimContext& ctx) {
  if (const Variable* var = ctx.FindVariable(name)) {
    return TypenameOfVariable(*var, name, writer);
  }
  if (const ClassObject* self = ctx.CurrentThis()) {
    if (const ClassMember* member = PropertyDeclaration(self->type, name)) {
      return writer.OfType(member->data_type, "", name);
    }
    if (const DataType* actual =
            TypeParamActual(self, self->type->decl, name)) {
      return writer.OfType(*actual, "", name);
    }
  }
  if (ctx.FindTypeDeclaration(name) != nullptr ||
      !ctx.FindPackageTypedefKey(name).empty()) {
    DataType reference;
    reference.kind = DataTypeKind::kNamed;
    reference.type_name = name;
    return writer.OfType(reference, "", name);
  }
  return {};
}

// A select of one element of an unpacked array or queue, `q[0]` of a
// property `string q[$]` or of a variable `AB_t AB[10]`, as $typename writes
// it: the element type, which is the declared type without the dimension the
// select takes away; empty where `arg` is no such select.
std::string TypenameOfElement(const Expr* arg, TypenameWriter& writer,
                              SimContext& ctx) {
  if (arg->kind != ExprKind::kSelect || arg->index_end != nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string_view name = arg->base->text;
  if (const Variable* var = ctx.FindVariable(name)) {
    if (var->declared_type == nullptr || var->declared_unpacked.empty()) {
      return {};
    }
    return writer.OfType(*var->declared_type, var->declared_scope, name) +
           ElementDimsText(var->declared_unpacked);
  }
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return {};
  const ClassMember* member = PropertyDeclaration(self->type, name);
  if (member == nullptr || member->unpacked_dims.size() != 1) return {};
  return writer.OfType(member->data_type, "", name);
}

}  // namespace

Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "logic");
  const Expr* arg = expr->args[0];
  TypenameEnvironment env = SimTypenameEnvironment(ctx, arena);
  TypenameWriter writer(env);
  if (arg->kind == ExprKind::kTypeRef && arg->type_value != nullptr) {
    return StringToLogic4Vec(arena,
                             writer.OfType(*arg->type_value, "", "type"));
  }
  if (std::optional<DataType> keyword = KeywordTypeOf(arg)) {
    return StringToLogic4Vec(arena, writer.OfType(*keyword, "", "type"));
  }
  std::string text = arg->kind == ExprKind::kIdentifier
                         ? TypenameOfIdentifier(arg->text, writer, ctx)
                         : TypenameOfElement(arg, writer, ctx);
  if (text.empty() && arg->kind != ExprKind::kIdentifier) {
    text = TypenameOfOperation(arg, env);
  }
  if (!text.empty()) return StringToLogic4Vec(arena, text);
  return EvalTypenameOfExpression(expr, ctx, arena);
}

}  // namespace delta
