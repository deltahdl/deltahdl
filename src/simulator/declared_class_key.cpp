#include "simulator/declared_class_key.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/sim_context.h"

namespace delta {

constexpr std::string_view kStdPackage = "std";

std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena) {
  std::string_view scope = type.scope_name;
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  if (!scope.empty() && scope != kStdPackage) {
    auto* scoped = arena.Create<std::string>(std::string(scope) +
                                             "::" + std::string(name));
    if (ctx.FindClassType(*scoped) != nullptr) return *scoped;
  }
  if (ctx.FindClassType(name) != nullptr) return name;
  if (scope.empty()) {
    if (const ClassTypeInfo* cls = ClassNamedByTypeParam(name, ctx, arena))
      return cls->name;
  }
  return {};
}

static std::string_view NestedClassKeyInScope(std::string_view name,
                                              const ClassTypeInfo* scope,
                                              SimContext& ctx, Arena& arena) {
  for (const ClassTypeInfo* t = scope; t != nullptr; t = t->enclosing) {
    auto* key = arena.Create<std::string>(std::string(t->name) +
                                          "::" + std::string(name));
    if (ctx.FindClassType(*key) != nullptr) return *key;
  }
  return {};
}

static bool IsTypeOfThis(const DataType& type) {
  const Expr* ref = type.type_ref_expr;
  return ref != nullptr && ref->kind == ExprKind::kIdentifier &&
         ref->text == "this";
}

std::string_view DeclaredClassKeyInScope(const DataType& type,
                                         const ClassTypeInfo* declaring,
                                         SimContext& ctx, Arena& arena) {
  if (IsTypeOfThis(type))
    return declaring != nullptr ? declaring->name : std::string_view{};
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  if (!type.scope_name.empty()) return DeclaredClassKey(type, ctx, arena);
  std::string_view nested = NestedClassKeyInScope(name, declaring, ctx, arena);
  return !nested.empty() ? nested : DeclaredClassKey(type, ctx, arena);
}

const DataType* TypeOfThisNamed(const DataType* type, const ClassTypeInfo* cls,
                                SimContext& ctx) {
  if (cls == nullptr || !IsTypeOfThis(*type)) return type;
  auto* named = ctx.GetArena().Create<DataType>();
  named->kind = DataTypeKind::kNamed;
  named->type_name = cls->name;
  return named;
}

}  // namespace delta
