#include "simulator/eval_class_params.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// The declared type of the class's i-th value parameter, or null where the
// declaration records none or the parameter is a type parameter, whose entry
// is its default type and sizes no value.
static const DataType* ParamType(const ClassDecl* decl, size_t i) {
  if (decl == nullptr || i >= decl->param_types.size() ||
      i >= decl->params.size() ||
      decl->type_param_names.count(decl->params[i].first) != 0)
    return nullptr;
  return &decl->param_types[i];
}

Logic4Vec ClassParamSizer::Value(size_t i, const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  std::string_view name = decl_ != nullptr && i < decl_->params.size()
                              ? decl_->params[i].first
                              : "";
  return Value(name, ParamType(decl_, i), expr, ctx, arena);
}

// §6.20.2 with §6.19: a default written as an enumeration's literal,
// `localparam Colors LC = green`, names a constant of the scope the class is
// declared in, whose storage a module creates after its classes are lowered
// (Lowerer::LowerModule), so that reading the name found nothing and the
// parameter held 0. The literal is read off the enumeration declaring it
// while no variable of the name exists yet.
static bool TryEnumLiteralDefault(const Expr* expr, SimContext& ctx,
                                  uint64_t& value) {
  if (expr == nullptr || expr->kind != ExprKind::kIdentifier ||
      !expr->scope_prefix.empty() || ctx.FindVariable(expr->text) != nullptr) {
    return false;
  }
  const EnumTypeInfo* info = ctx.FindEnumTypeDeclaringMember(expr->text, {});
  if (info == nullptr) return false;
  for (const EnumMemberInfo& m : info->members) {
    if (m.name != expr->text) continue;
    value = m.value;
    return true;
  }
  return false;
}

static Logic4Vec ParamDefaultValue(const Expr* expr, uint32_t width,
                                   SimContext& ctx, Arena& arena) {
  uint64_t literal = 0;
  if (TryEnumLiteralDefault(expr, ctx, literal))
    return MakeLogic4VecVal(arena, width == 0 ? 32 : width, literal);
  return width == 0
             ? EvalExpr(expr, ctx, arena)
             : ResizeToWidth(EvalExpr(expr, ctx, arena, width), width, arena);
}

Logic4Vec ClassParamSizer::Value(std::string_view name, const DataType* type,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  uint32_t width = 0;
  if (type != nullptr && type->kind != DataTypeKind::kReal &&
      type->kind != DataTypeKind::kShortreal &&
      type->kind != DataTypeKind::kRealtime)
    width = DeclaredParamTypeWidth(*type, scope_);
  Logic4Vec val = ParamDefaultValue(expr, width, ctx, arena);
  if (!name.empty() && !val.is_real)
    scope_[name] = static_cast<int64_t>(val.ToUint64());
  return val;
}

void ClassParamSizer::Record(size_t i, const Logic4Vec& val) {
  if (decl_ == nullptr || i >= decl_->params.size() || val.is_real) return;
  scope_[decl_->params[i].first] = static_cast<int64_t>(val.ToUint64());
}

const DataType* ActualForParam(const std::vector<DataType>& actuals, size_t i,
                               std::string_view pname) {
  for (const auto& actual : actuals) {
    if (actual.param_arg_name == pname) return &actual;
  }
  if (i < actuals.size() && actuals[i].param_arg_name.empty())
    return &actuals[i];
  return nullptr;
}

// §8.25: binds each type parameter of the object's class to the type the
// variable's declaration wrote for it, so that a property declared with the
// parameter as its type or as its associative index -- uvm_pool's `T
// pool[KEY]` -- is read with the bound type rather than with the name. A type
// actual is no expression, so the value loop below cannot carry it.
//
// Nothing is bound for a declaration that wrote no list, which is §8.25.1's
// default specialization and reads the defaults; the specialization the
// object's own type may be is bound ahead of this, as the object is created
// (BindSpecializationTypeParams below).
static void BindTypeParamActuals(ClassObject* obj,
                                 const std::vector<DataType>* actuals) {
  if (actuals == nullptr) return;
  const ClassDecl& decl = *obj->type->decl;
  for (size_t i = 0; i < decl.params.size(); ++i) {
    std::string_view pname = decl.params[i].first;
    if (decl.type_param_names.count(pname) == 0) continue;
    if (const DataType* actual = ActualForParam(*actuals, i, pname))
      obj->type_param_actuals[std::string(pname)] = actual;
  }
}

void BindSpecializationTypeParams(ClassObject* obj) {
  if (obj == nullptr || obj->type == nullptr || obj->type->decl == nullptr)
    return;
  BindTypeParamActuals(obj, obj->type->param_actuals);
}

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const std::vector<DataType>* actuals =
      ctx.FindVariableClassTypeParams(var_name);
  // §8.25 (printed page 204 of IEEE 1800-2023): the value parameters belong
  // to the specialization as the type parameters do, so a name reaching the
  // specialization while writing no list of its own -- `typedef V#(4) v4;`,
  // on which `v4 x = new` writes nothing -- is answered by the list the type
  // carries. Without it the loop below was skipped whole and the object kept
  // the declaration's default, `x.w()` reading V's 1 rather than 4.
  if (actuals == nullptr) actuals = obj->type->param_actuals;
  BindTypeParamActuals(obj, actuals);
  if (actuals == nullptr) return;
  const auto& params = obj->type->decl->params;
  // §8.25 with §6.20.2 and §23.10.2: an actual is converted to the
  // parameter's declared type (ClassParamSizer), `'hfff0` for a `logic
  // [W-1:0]` under `#(12, 'hfff0)` cut to the 12-bit ff0; a parameter the
  // list leaves at its default keeps the default the construction stored,
  // recorded for the ranges after it.
  ClassParamSizer sizer(obj->type->decl);
  for (size_t i = 0; i < params.size(); ++i) {
    // §23.10.2.2 through §8.25: a value actual is matched to its parameter
    // as a type actual is, by the name it was written with or else by its
    // position; a type actual carries no expression and is left to
    // BindTypeParamActuals above.
    const DataType* actual = ActualForParam(*actuals, i, params[i].first);
    if (actual == nullptr || actual->type_ref_expr == nullptr) {
      auto kept = obj->properties.find(std::string(params[i].first));
      if (kept != obj->properties.end()) sizer.Record(i, kept->second);
      continue;
    }
    // §6.8, as in the default arm of InitClassPropertyDefaults in
    // eval_class_new.cpp: the object's stored parameter and whatever the
    // override expression read are two data storage elements, and a
    // Logic4Vec copy carries the words pointer rather than the words, so
    // `C #(.W(n)) c;` stored as it arrived left the object and the variable
    // n as one buffer. One copy serves both keys, which are two names for
    // the one parameter.
    auto val =
        OwnRhsWords(sizer.Value(i, actual->type_ref_expr, ctx, arena), arena);
    obj->properties[std::string(params[i].first)] = val;
    std::string scoped =
        std::string(obj->type->name) + "::" + std::string(params[i].first);
    obj->properties[scoped] = val;
  }
}

std::vector<ClassParamBinding> CollectClassParamBindings(
    const ClassTypeInfo* cls, SimContext& ctx) {
  std::vector<ClassParamBinding> bindings;
  if (cls == nullptr || cls->decl == nullptr) return bindings;
  for (const auto& [pname, pexpr] : cls->decl->params) {
    ClassParamBinding b{pname, ctx.FindLocalVariable(pname),
                        ctx.FindScopeTypeActual(pname)};
    if (b.value != nullptr || b.type != nullptr) bindings.push_back(b);
    std::string qualified =
        std::string(cls->decl->name) + "." + std::string(pname);
    if (Variable* qv = ctx.FindLocalVariable(qualified)) {
      auto* key = ctx.GetArena().Create<std::string>(qualified);
      bindings.push_back({*key, qv, nullptr});
    }
  }
  return bindings;
}

void RebindClassParamBindings(const std::vector<ClassParamBinding>& bindings,
                              SimContext& ctx) {
  for (const ClassParamBinding& b : bindings) {
    if (b.value != nullptr) ctx.BindLocalVariable(b.name, b.value);
    if (b.type != nullptr) ctx.BindScopeTypeActual(b.name, b.type);
  }
}

}  // namespace delta
