// The type comparison §12.8's and §18.17.7's return checks share, declared in
// return_value_fit.h. Split out of elaborator_validate_jump_statements.cpp,
// which keeps §12.8's walk over a function's returns, so that
// elaborator_validate_randsequence.cpp reads a production's returns with it.

#include "elaborator/return_value_fit.h"

#include <cstddef>
#include <string_view>
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
#include "parser/ast_stmt.h"
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

// The unpacked dimensions of a variable written with none: a for loop's
// declared variable and a foreach loop variable.
const std::vector<Expr*>* NoUnpackedDims() {
  static const std::vector<Expr*> kNone;
  return &kNone;
}

// §12.7.1: the variables the initialization of for loop `s` declares, each
// with the data type written before it. Stmt::for_init_types holds
// DataTypeKind::kImplicit for an item that assigns a variable declared outside
// the loop rather than declaring one; Parser::ParseForLocalDeclInits and
// Parser::ParseForPlainInits push one type for each item. An item with no
// left-hand side is one the parser could not read as an assignment.
void EnterForLocals(const Stmt* s, DeclaredLocals& locals) {
  for (size_t i = 0; i < s->for_init_types.size(); ++i) {
    const Stmt* init = s->for_inits[i];
    if (s->for_init_types[i].kind == DataTypeKind::kImplicit ||
        init->lhs == nullptr)
      continue;
    locals[init->lhs->text] = {&s->for_init_types[i], NoUnpackedDims()};
  }
}

// §12.7.3: whether the dimension the `rank`th loop variable of a foreach over
// `array` walks is a fixed-size, dynamic or queue dimension, the ones over
// which the loop variable is an int. Its unpacked dimensions come first, then
// the packed dimensions of its type. Parser::ParseUnpackedDims writes a dynamic
// dimension as null and every associative one as an identifier, its index
// type or `*`, which a parameter naming a fixed size is too, so an identifier
// other than a queue's `$` is not plainly any of the three.
bool WalksIntIndexedDim(const DeclaredLocal& array, size_t rank) {
  if (rank >= array.unpacked->size())
    return array.type->kind != DataTypeKind::kNamed;
  const Expr* dim = (*array.unpacked)[rank];
  return dim == nullptr || dim->kind != ExprKind::kIdentifier ||
         dim->text == "$";
}

// §12.7.3: the loop variables of foreach loop `s`, each an int where the
// dimension it walks is plainly one an int indexes and otherwise a name whose
// type the check does not read. The array's entry is copied before any loop
// variable is entered, since a loop variable may share its name and the array
// is read in the scope around the loop.
void EnterForeachLocals(const Stmt* s, DeclaredLocals& locals) {
  static const DataType kLoopIndex = [] {
    DataType t;
    t.kind = DataTypeKind::kInt;
    return t;
  }();
  DeclaredLocal array{nullptr, nullptr};
  if (s->expr->kind == ExprKind::kIdentifier) {
    auto it = locals.find(s->expr->text);
    if (it != locals.end()) array = it->second;
  }
  for (size_t i = 0; i < s->foreach_vars.size(); ++i) {
    std::string_view var = s->foreach_vars[i];
    if (var.empty()) continue;
    if (array.type != nullptr && WalksIntIndexedDim(array, i))
      locals[var] = {&kLoopIndex, NoUnpackedDims()};
    else
      locals.erase(var);
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

void EnterDeclaredLocals(const std::vector<Stmt*>& items,
                         DeclaredLocals& locals) {
  for (const Stmt* s : items) {
    if (s->kind == StmtKind::kVarDecl)
      locals[s->var_name] = {&s->var_decl_type, &s->var_unpacked_dims};
  }
}

bool OpensScope(const Stmt* s) {
  return s->kind == StmtKind::kBlock || s->kind == StmtKind::kFor ||
         s->kind == StmtKind::kForeach;
}

void EnterScopeLocals(const Stmt* s, DeclaredLocals& locals) {
  if (s->kind == StmtKind::kBlock) {
    EnterDeclaredLocals(s->stmts, locals);
  } else if (s->kind == StmtKind::kFor) {
    EnterForLocals(s, locals);
  } else {
    EnterForeachLocals(s, locals);
  }
}

CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx) {
  if (e->kind == ExprKind::kIdentifier) {
    auto it = ctx.locals.find(e->text);
    if (it == ctx.locals.end() || !it->second.unpacked->empty())
      return CheckedType{};
    return CheckedTypeOf(*it->second.type, ctx);
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
