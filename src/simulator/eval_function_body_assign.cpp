#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static bool IsMemberAccessOn(const Expr* lhs, std::string_view base_name) {
  return lhs->kind == ExprKind::kMemberAccess && lhs->lhs &&
         lhs->lhs->kind == ExprKind::kIdentifier &&
         lhs->lhs->text == base_name && lhs->rhs &&
         lhs->rhs->kind == ExprKind::kIdentifier;
}

static void WriteSelfProperty(ClassObject* self, std::string_view name,
                              const Logic4Vec& val, SimContext& ctx,
                              Arena& arena) {
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) enclosing = self->type;
  Logic4Vec stored = CoerceToPropertyType(enclosing, name, val, arena);
  if (enclosing) {
    self->SetPropertyForType(name, enclosing, stored);
  } else {
    self->SetProperty(std::string(name), stored);
  }
  ctx.NotifyClassHandleWatchers(self->handle);
}

bool TryFuncClassPropertyWrite(const Expr* lhs, const Logic4Vec& val,
                               SimContext& ctx, Arena& arena) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassTypeInfo* owner = method_cls != nullptr
                                   ? method_cls->StaticPropertyOwner(lhs->text)
                                   : nullptr;
  if (owner != nullptr) {
    owner->static_properties[std::string(lhs->text)] = val;
    owner->NotifyStaticWatchers();
    return true;
  }
  auto* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  WriteSelfProperty(self, lhs->text, val, ctx, arena);
  return true;
}

static bool TryStaticClassNewAssign(const Stmt* stmt,
                                    std::string_view field_name,
                                    SimContext& ctx, Arena& arena) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassTypeInfo* owner = method_cls != nullptr
                                   ? method_cls->StaticPropertyOwner(field_name)
                                   : nullptr;
  if (owner == nullptr) return false;
  auto field_type = MemberClassTypeName(owner, field_name);
  if (field_type.empty() || ctx.FindClassType(field_type) == nullptr)
    return false;
  Logic4Vec handle =
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  owner->static_properties[std::string(field_name)] = handle;
  owner->NotifyStaticWatchers();
  return true;
}

static bool TrySelfClassNewAssign(const Stmt* stmt, std::string_view field_name,
                                  SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (TryStaticClassNewAssign(stmt, field_name, ctx, arena)) return true;
  auto* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  auto field_type = PropertyClassName(self, enclosing, field_name, ctx);
  if (field_type.empty()) return false;
  WriteSelfProperty(
      self, field_name,
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start),
      ctx, arena);
  return true;
}

static bool TryFuncClassTargetWrite(const Expr* lhs, const Logic4Vec& val,
                                    SimContext& ctx, Arena& arena);

static bool TryFuncCompoundOnClassTarget(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  const Expr* lhs = stmt->lhs;
  bool declared =
      lhs->kind == ExprKind::kIdentifier && NameDenotesVariable(lhs->text, ctx);
  if (declared || (lhs->kind != ExprKind::kIdentifier &&
                   lhs->kind != ExprKind::kMemberAccess)) {
    return false;
  }
  Logic4Vec current = EvalExpr(lhs, ctx, arena);
  Logic4Vec operand = EvalExpr(stmt->rhs->rhs, ctx, arena);
  Logic4Vec val = OwnRhsWords(EvalBinaryOp(CompoundAssignBaseOp(stmt->rhs->op),
                                           current, operand, arena),
                              arena);
  if (!TryFuncClassTargetWrite(lhs, val, ctx, arena))
    ApplyGenericBlockingAssign(stmt, val, ctx, arena);
  return true;
}

static bool TryFuncCompoundAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->rhs == nullptr || stmt->rhs->kind != ExprKind::kBinary ||
      !IsCompoundAssignOp(stmt->rhs->op) || stmt->rhs->is_parenthesized) {
    return false;
  }
  if (TryFuncCompoundOnClassTarget(stmt, ctx, arena)) return true;
  ApplyCompoundAssignOp(stmt, ctx, arena);
  return true;
}

static bool TryFuncSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (TryFuncCompoundAssign(stmt, ctx, arena)) return true;
  if (TryClassArrayNewAssign(stmt, ctx, arena)) return true;
  if (stmt->lhs->kind == ExprKind::kIdentifier &&
      !NameDenotesVariable(stmt->lhs->text, ctx) &&
      TrySelfClassNewAssign(stmt, stmt->lhs->text, ctx, arena))
    return true;
  if (IsMemberAccessOn(stmt->lhs, "this") && stmt->lhs->rhs &&
      TrySelfClassNewAssign(stmt, stmt->lhs->rhs->text, ctx, arena))
    return true;
  if (TryClassNewAssign(stmt, ctx, arena)) return true;
  if (TryClassArrayWholeAssign(stmt, ctx, arena)) return true;
  return TryQueueBlockingAssign(stmt, ctx, arena);
}

static bool TryFuncClassTargetWrite(const Expr* lhs, const Logic4Vec& val,
                                    SimContext& ctx, Arena& arena) {
  if (IsMemberAccessOn(lhs, "this")) {
    auto* self = ctx.CurrentThis();
    if (self) WriteSelfProperty(self, lhs->rhs->text, val, ctx, arena);
    return true;
  }
  if (IsMemberAccessOn(lhs, "super")) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(
          std::string(lhs->rhs->text), self->type->parent,
          CoerceToPropertyType(self->type->parent, lhs->rhs->text, val, arena));
      ctx.NotifyClassHandleWatchers(self->handle);
    }
    return true;
  }
  if (lhs->kind == ExprKind::kIdentifier &&
      !NameDenotesVariable(lhs->text, ctx)) {
    return TryFuncClassPropertyWrite(lhs, val, ctx, arena);
  }
  return false;
}

void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs) return;
  if (TryCallResultArrayAssign(stmt, ctx, arena)) return;
  if (TryFuncSpecialBlockingAssign(stmt, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->text == ctx.CurrentFuncName()) {
    RecordReturnedTag(stmt->rhs);
  }
  if (TryDispatchSpecialBlockingAssign(stmt, ctx, arena)) return;
  LhsIndexPin pin(TaggedElementTarget(stmt), ctx, arena);
  Logic4Vec val =
      OwnRhsWords(EvalRhsCarryingReturnedTag(stmt, ctx, arena), arena);
  if (TryFuncClassTargetWrite(stmt->lhs, val, ctx, arena)) {
    RecordPropertyTags(stmt, ctx, arena);
    return;
  }
  ApplyGenericBlockingAssign(stmt, val, ctx, arena);
}

void ShapeStringReturnVariable(const ModuleItem* func, Variable* ret_var,
                               SimContext& ctx, Arena& arena) {
  if (ret_var->is_string || !DeclaredTypeIsString(func->return_type, ctx))
    return;
  ret_var->is_string = true;
  ret_var->value = MakeLogic4VecVal(arena, 0, 0);
}

void ShapeClassReturnVariable(const ModuleItem* func, Variable* ret_var,
                              SimContext& ctx, Arena& arena) {
  if (func->return_type.kind != DataTypeKind::kNamed) return;
  std::string_view class_key = DeclaredClassKeyInScope(
      func->return_type, ctx.CurrentMethodClass(), ctx, arena);
  if (class_key.empty()) return;
  ctx.SetVariableClassType(func->name, class_key);
  if (ret_var->value.width != 64)
    ret_var->value = MakeLogic4VecVal(arena, 64, 0);
}

bool TryFuncReturnClassNew(Expr* returned, std::string_view func_name,
                           SimContext& ctx, Arena& arena) {
  if (returned->kind != ExprKind::kCall || returned->text != "new")
    return false;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->range = returned->range;
  assign->lhs = arena.Create<Expr>();
  assign->lhs->kind = ExprKind::kIdentifier;
  assign->lhs->range = returned->range;
  assign->lhs->text = func_name;
  assign->rhs = returned;
  return TryClassNewAssign(assign, ctx, arena);
}

}  // namespace delta
