#include "elaborator/return_value_fit.h"

#include <cstddef>
#include <functional>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/class_member_names.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
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

const std::vector<Expr*>* NoUnpackedDims() {
  static const std::vector<Expr*> kNone;
  return &kNone;
}

void EnterForLocals(const Stmt* s, DeclaredLocals& locals) {
  for (size_t i = 0; i < s->for_init_types.size(); ++i) {
    const Stmt* init = s->for_inits[i];
    if (s->for_init_types[i].kind == DataTypeKind::kImplicit ||
        init->lhs == nullptr)
      continue;
    locals[init->lhs->text] = {&s->for_init_types[i], NoUnpackedDims()};
  }
}

bool WalksIntIndexedDim(const DeclaredLocal& array, size_t rank) {
  if (rank >= array.unpacked->size())
    return array.type->kind != DataTypeKind::kNamed;
  const Expr* dim = (*array.unpacked)[rank];
  return dim == nullptr || dim->kind != ExprKind::kIdentifier ||
         dim->text == "$";
}

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

bool OpensScope(const Stmt* s) {
  return s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork ||
         s->kind == StmtKind::kFor || s->kind == StmtKind::kForeach;
}

void EnterScopeLocals(const Stmt* s, DeclaredLocals& locals) {
  if (s->kind == StmtKind::kBlock) {
    EnterDeclaredLocals(s->stmts, locals);
  } else if (s->kind == StmtKind::kFork) {
    EnterDeclaredLocals(s->fork_stmts, locals);
  } else if (s->kind == StmtKind::kFor) {
    EnterForLocals(s, locals);
  } else {
    EnterForeachLocals(s, locals);
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

void ForEachChildInScope(
    const Stmt* s, const ReturnCtx& ctx,
    const std::function<void(const Stmt*, const ReturnCtx&)>& visit) {
  const bool kOpens = OpensScope(s);
  ReturnCtx scope_ctx{ctx.typedefs, ctx.unit, {}};
  if (kOpens) {
    scope_ctx.locals = ctx.locals;
    EnterScopeLocals(s, scope_ctx.locals);
  }
  const ReturnCtx& inner = kOpens ? scope_ctx : ctx;
  ForEachChildStmt(s, [&](const Stmt* sub) { visit(sub, inner); });
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

namespace {

void EnterClassMethods(const ClassDecl* cls, ClassMethods& methods) {
  if (cls == nullptr) return;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      methods[m->method] = cls;
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      EnterClassMethods(m->nested_class, methods);
    }
  }
}

}  // namespace

ClassMethods ClassMethodsOf(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit) {
  ClassMethods methods;
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl)
      EnterClassMethods(item->class_decl, methods);
  }
  if (unit != nullptr) {
    for (const auto* cls : unit->classes) EnterClassMethods(cls, methods);
  }
  return methods;
}

DeclaredLocals ClassProperties(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  std::vector<const ClassDecl*> chain;
  for (; cls != nullptr; cls = FindBaseClass(cls, unit)) chain.push_back(cls);
  DeclaredLocals properties;
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    for (const ClassMember* m : (*it)->members) {
      if (m->kind == ClassMemberKind::kProperty && !m->is_param)
        properties[m->name] = {&m->data_type, &m->unpacked_dims};
    }
  }
  return properties;
}

DeclaredLocals ScopeVariables(const std::vector<ModuleItem*>& items) {
  DeclaredLocals variables;
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kVarDecl)
      variables[item->name] = {&item->data_type, &item->unpacked_dims};
  }
  return variables;
}

namespace {

void EnterClassScope(const ClassDecl* cls, const DeclaredLocals& around,
                     const SoleClassIndex& classes, const CompilationUnit& unit,
                     ClassScopes& scopes) {
  DeclaredLocals names;
  std::unordered_set<std::string_view> declared;
  if (classes.SelectableNames(*cls, declared)) {
    for (const auto& [name, variable] : around) {
      if (!declared.contains(name)) names.emplace(name, variable);
    }
  }
  for (const auto& [name, property] : ClassProperties(cls, &unit)) {
    names[name] = property;
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kClassDecl)
      EnterClassScope(m->nested_class, names, classes, unit, scopes);
  }
  scopes[cls] = std::move(names);
}

}  // namespace

ClassScopes ClassScopesOf(const std::vector<ModuleItem*>& items,
                          const CompilationUnit& unit) {
  ClassScopes scopes;
  const SoleClassIndex kClasses(unit);
  const DeclaredLocals kAround = ScopeVariables(items);
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl)
      EnterClassScope(item->class_decl, kAround, kClasses, unit, scopes);
  }
  const DeclaredLocals kUnitAround = ScopeVariables(unit.cu_items);
  for (const auto* cls : unit.classes) {
    EnterClassScope(cls, kUnitAround, kClasses, unit, scopes);
  }
  return scopes;
}

DeclaredLocals SubroutineLocals(const ModuleItem* item,
                                const DeclaredLocals& outer) {
  DeclaredLocals locals = outer;
  for (const auto& arg : item->func_args)
    locals[arg.name] = {&arg.data_type, &arg.unpacked_dims};
  EnterDeclaredLocals(item->func_body_stmts, locals);
  return locals;
}

SubroutineScopes::SubroutineScopes(const std::vector<ModuleItem*>& items,
                                   const TypedefMap& typedefs,
                                   const CompilationUnit& unit)
    : methods_(ClassMethodsOf(items, &unit)),
      classes_(ClassScopesOf(items, unit)),
      unit_(&unit),
      outside_{typedefs, &unit, ScopeVariables(items)} {}

bool SubroutineScopes::IsMethod(const ModuleItem* item) const {
  return methods_.contains(item) || !item->method_class.empty();
}

ReturnCtx SubroutineScopes::Around(const ModuleItem* item) {
  static const TypedefMap kNoTypedefs;
  if (!IsMethod(item)) return outside_;
  const auto kMethod = methods_.find(item);
  const ClassDecl* cls = kMethod != methods_.end()
                             ? kMethod->second
                             : FindClassDecl(item->method_class, unit_);
  return {kNoTypedefs, unit_, classes_[cls]};
}

}  // namespace delta
