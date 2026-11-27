#include "simulator/eval_class_scope_types.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_spelled_by.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/class_specialization_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

const Expr* SpecializationElement(const Expr& base, size_t pos,
                                  std::string_view pname) {
  for (size_t j = 0; j < base.elements.size(); ++j) {
    if (j < base.arg_names.size() && base.arg_names[j] == pname)
      return base.elements[j];
  }
  if (pos >= base.elements.size()) return nullptr;
  bool named = pos < base.arg_names.size() && !base.arg_names[pos].empty();
  return named ? nullptr : base.elements[pos];
}

static void BindSpecializationTypeActuals(const ClassTypeInfo* spec,
                                          SimContext& ctx) {
  const ClassDecl* decl = spec->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual = ActualForParam(*spec->param_actuals, i, pname);
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit) continue;
    ctx.BindScopeTypeActual(pname, actual);
  }
}

void BindClassScopeTypeActuals(const ClassTypeInfo* cls, const Expr* base,
                               SimContext& ctx, Arena& arena) {
  if (cls == nullptr || cls->decl == nullptr || base == nullptr) return;
  if (cls->param_actuals != nullptr) {
    BindSpecializationTypeActuals(cls, ctx);
    return;
  }
  const ClassDecl* decl = cls->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const Expr* elem = SpecializationElement(*base, i, pname);
    if (elem == nullptr) continue;
    DataType dt = TypeSpelledBy(elem);
    if (dt.kind == DataTypeKind::kImplicit) continue;
    ctx.BindScopeTypeActual(pname, arena.Create<DataType>(dt));
  }
}

void BindStaticInitTypeActuals(const ClassTypeInfo* cls, SimContext& ctx) {
  if (cls == nullptr || cls->decl == nullptr) return;
  const ClassDecl* decl = cls->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual = cls->param_actuals != nullptr
                                 ? ActualForParam(*cls->param_actuals, i, pname)
                                 : nullptr;
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit)
      actual = TypeParamActual(nullptr, decl, pname);
    if (actual != nullptr) ctx.BindScopeTypeActual(pname, actual);
  }
}

uint32_t ScopedTypeParamWidth(std::string_view name, SimContext& ctx) {
  if (const DataType* bound = ctx.FindScopeTypeActual(name))
    return DeclaredTypeWidth(*bound, ctx);
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (cls == nullptr || cls->decl == nullptr ||
      cls->decl->type_param_names.count(name) == 0) {
    return 0;
  }
  const DataType* def = TypeParamActual(nullptr, cls->decl, name);
  return def != nullptr ? DeclaredTypeWidth(*def, ctx) : 0;
}

static const DataType* RunningClassTypeParam(std::string_view name,
                                             SimContext& ctx) {
  if (const DataType* bound = ctx.FindScopeTypeActual(name)) return bound;
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (cls == nullptr || cls->decl == nullptr) return nullptr;
  const ClassDecl* decl = cls->decl;
  if (decl->type_param_names.count(name) == 0) return nullptr;
  for (size_t i = 0; cls->param_actuals != nullptr && i < decl->params.size();
       ++i) {
    if (decl->params[i].first != name) continue;
    const DataType* actual = ActualForParam(*cls->param_actuals, i, name);
    if (actual != nullptr && actual->kind != DataTypeKind::kImplicit)
      return actual;
  }
  return TypeParamActual(ctx.CurrentThis(), decl, name);
}

static const ClassMember* RunningClassProperty(std::string_view name,
                                               SimContext& ctx) {
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (cls == nullptr || cls->decl == nullptr || cls->decl->params.empty())
    return nullptr;
  for (const ClassMember* m : cls->decl->members) {
    if (m->kind == ClassMemberKind::kProperty && !m->is_param &&
        m->name == name)
      return m;
  }
  return nullptr;
}

static bool IsBareTypeName(const DataType& type) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty() &&
         type.packed_dim_left == nullptr && type.extra_packed_dims.empty() &&
         type.type_params.empty();
}

static std::string_view WrittenName(const Expr* op) {
  if (op->type_value != nullptr)
    return IsBareTypeName(*op->type_value) ? op->type_value->type_name
                                           : std::string_view{};
  if (op->lhs != nullptr && op->lhs->kind == ExprKind::kIdentifier &&
      op->lhs->scope_prefix.empty())
    return op->lhs->text;
  return {};
}

struct RunningOperandType {
  DataType type;
  bool through_class = false;
  uint32_t held_width = 0;
};

static uint32_t HeldWidth(std::string_view name, SimContext& ctx) {
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return 0;
  auto held = self->properties.find(std::string(name));
  return held != self->properties.end() ? held->second.width : 0;
}

static std::optional<RunningOperandType> PropertyType(const ClassMember& prop,
                                                      SimContext& ctx) {
  if (!prop.unpacked_dims.empty()) return std::nullopt;
  const DataType* actual =
      IsBareTypeName(prop.data_type)
          ? RunningClassTypeParam(prop.data_type.type_name, ctx)
          : nullptr;
  if (actual != nullptr) return RunningOperandType{*actual, true};
  return RunningOperandType{prop.data_type, true, HeldWidth(prop.name, ctx)};
}

static std::optional<RunningOperandType> TypeOfRunningOperand(const Expr* op,
                                                              SimContext& ctx) {
  const std::string_view kName = WrittenName(op);
  if (!kName.empty()) {
    if (const DataType* actual = RunningClassTypeParam(kName, ctx))
      return RunningOperandType{*actual, true};
    if (const ClassMember* prop = RunningClassProperty(kName, ctx))
      return PropertyType(*prop, ctx);
  }
  if (op->type_value == nullptr) return std::nullopt;
  return RunningOperandType{*op->type_value};
}

std::optional<bool> RunningClassTypeRefsMatch(const Expr* a, const Expr* b,
                                              SimContext& ctx) {
  std::optional<RunningOperandType> type_a = TypeOfRunningOperand(a, ctx);
  std::optional<RunningOperandType> type_b = TypeOfRunningOperand(b, ctx);
  if (!type_a || !type_b || (!type_a->through_class && !type_b->through_class))
    return std::nullopt;
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  return TypeKeySeenFrom(type_a->type, from, type_a->held_width, ctx) ==
         TypeKeySeenFrom(type_b->type, from, type_b->held_width, ctx);
}

uint32_t SpecializationTypeParamWidth(const Expr* scope, SimContext& ctx,
                                      Arena& arena) {
  if (scope == nullptr || scope->kind != ExprKind::kMemberAccess ||
      !scope->is_scope_resolution || scope->rhs == nullptr ||
      scope->rhs->kind != ExprKind::kIdentifier) {
    return 0;
  }
  const ClassTypeInfo* spec = ScopeNamedSpecialization(scope->lhs, ctx, arena);
  if (spec == nullptr || spec->decl == nullptr ||
      spec->param_actuals == nullptr) {
    return 0;
  }
  const ClassDecl* decl = spec->decl;
  std::string_view pname = scope->rhs->text;
  if (decl->type_param_names.count(pname) == 0) return 0;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first != pname) continue;
    const DataType* actual = ActualForParam(*spec->param_actuals, i, pname);
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit)
      actual = TypeParamActual(nullptr, decl, pname);
    return actual != nullptr ? DeclaredTypeWidth(*actual, ctx) : 0;
  }
  return 0;
}

}  // namespace delta
