// The type comparison §12.8's and §18.17.7's return checks share, declared in
// return_value_fit.h. Split out of elaborator_validate_jump_statements.cpp,
// which keeps §12.8's walk over a function's returns, so that
// elaborator_validate_randsequence.cpp reads a production's returns with it.

#include "elaborator/return_value_fit.h"

#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Map literal expression kinds whose type is obvious from the syntax alone
// to the corresponding DataTypeKind. Returns kImplicit when no narrow
// classification is possible without full expression type inference. §5.9
// makes a string literal in an assignment an unsigned integer constant, eight
// bits a character, so it maps to a bit vector.
DataTypeKind ObviousLiteralKind(const Expr* e) {
  if (!e) return DataTypeKind::kImplicit;
  switch (e->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kBit;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kTimeLiteral:
      return DataTypeKind::kTime;
    default:
      return DataTypeKind::kImplicit;
  }
}

}  // namespace

CheckedType CheckedTypeOf(const DataType& declared, const ReturnCtx& ctx) {
  const DataType& t = LastTypeInChain(declared, ctx.typedefs);
  CheckedType out;
  if (t.kind != DataTypeKind::kNamed) {
    out.type = t;
  } else if (ctx.unit != nullptr) {
    out.cls = ClassOfDeclaredType(t, {}, ctx.unit);
  }
  return out;
}

CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx) {
  if (e->kind == ExprKind::kIdentifier) {
    auto it = ctx.locals.find(e->text);
    return it == ctx.locals.end() ? CheckedType{}
                                  : CheckedTypeOf(*it->second, ctx);
  }
  CheckedType out;
  out.type.kind = ObviousLiteralKind(e);
  out.is_string_literal = e->kind == ExprKind::kStringLiteral;
  return out;
}

bool ReturnValueFits(const CheckedType& ret, const CheckedType& value,
                     const CompilationUnit* unit) {
  if (value.is_string_literal && ret.type.kind == DataTypeKind::kString)
    return true;
  bool ret_read = ret.type.kind != DataTypeKind::kImplicit;
  bool value_read = value.type.kind != DataTypeKind::kImplicit;
  if (ret.cls != nullptr) {
    if (value.cls == nullptr) return !value_read;
    return value.cls == ret.cls ||
           IsClassDeclDerivedFrom(value.cls, ret.cls->name, unit);
  }
  if (value.cls != nullptr) return !ret_read;
  return !ret_read || !value_read ||
         IsAssignmentCompatible(value.type, ret.type);
}

std::unordered_set<const ModuleItem*> ClassMethodsOf(
    const std::vector<ModuleItem*>& items, const CompilationUnit* unit) {
  std::unordered_set<const ModuleItem*> methods;
  auto add_method = [&methods](const ModuleItem* m) { methods.insert(m); };
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl)
      ForEachClassBodyItem(item->class_decl, add_method);
  }
  if (unit != nullptr) {
    for (const auto* cls : unit->classes) ForEachClassBodyItem(cls, add_method);
  }
  return methods;
}

}  // namespace delta
