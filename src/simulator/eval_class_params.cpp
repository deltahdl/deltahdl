#include "simulator/eval_class_params.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static std::string TypeTableKey(const DataType& type) {
  if (type.scope_name.empty()) return std::string(type.type_name);
  return std::string(type.scope_name) + "::" + std::string(type.type_name);
}

uint32_t SimParamTypeWidth(const DataType& type, const ScopeMap& scope,
                           const SimContext& ctx) {
  uint32_t width = DeclaredParamTypeWidth(type, scope);
  if (width != 0 || type.kind != DataTypeKind::kNamed) return width;
  std::string key = TypeTableKey(type);
  const StructTypeInfo* aggregate = ctx.FindStructType(key);
  bool packed_aggregate = aggregate != nullptr && aggregate->is_packed;
  if (!packed_aggregate && !IsIntegralType(ctx.FindTypeKind(key))) return 0;
  uint32_t base = ctx.FindTypeWidth(key);
  uint32_t outer = PackedDimProduct(type, scope);
  return outer > 0 ? base * outer : base;
}

bool SimParamTypeIsSigned(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || type.packed_dim_left != nullptr)
    return type.is_signed;
  return ctx.FindTypeSigned(TypeTableKey(type));
}

static const DataType* ParamType(const ClassDecl* decl, size_t i) {
  if (decl == nullptr || i >= decl->param_types.size() ||
      i >= decl->params.size() ||
      decl->type_param_names.count(decl->params[i].first) != 0)
    return nullptr;
  return &decl->param_types[i];
}

static void ShapeParamLocal(const DataType* type, Variable* local,
                            SimContext& ctx, Arena& arena) {
  RecordPackedRange(type, local, ctx, arena);
  if (type != nullptr) local->local_layout = DeclaredTypeLayout(*type, ctx);
}

void ShapeClassParamLocal(const ClassDecl* decl, size_t i, Variable* local,
                          SimContext& ctx, Arena& arena) {
  ShapeParamLocal(ParamType(decl, i), local, ctx, arena);
}

Logic4Vec ClassParamSizer::Value(size_t i, const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  std::string_view name = decl_ != nullptr && i < decl_->params.size()
                              ? decl_->params[i].first
                              : "";
  return Value(name, ParamType(decl_, i), expr, ctx, arena);
}

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
  if (width == 0) return EvalExpr(expr, ctx, arena);
  Logic4Vec val = ConvertRealForKnownLhs(EvalExpr(expr, ctx, arena, width),
                                         false, width, arena);
  return ResizeToWidth(val, width, arena);
}

static Logic4Vec ParamValueOfType(const DataType& type, const Expr* expr,
                                  uint32_t width, SimContext& ctx,
                                  Arena& arena) {
  const Expr* pattern = expr != nullptr ? UnwrapTypedPattern(expr) : nullptr;
  const StructTypeInfo* layout =
      pattern != nullptr && pattern->kind == ExprKind::kAssignmentPattern
          ? NamedLayout(type, ctx)
          : nullptr;
  if (layout != nullptr)
    return EvalStructPatternValue(pattern, layout, ctx, arena);
  return ParamDefaultValue(expr, width, ctx, arena);
}

static DataType SizedParamType(std::string_view name, const DataType& type,
                               const ClassDecl& decl, std::string_view scope,
                               SimContext& ctx) {
  std::string_view in_place =
      InPlaceAggregateLayoutKey(decl.name, name, type, ctx);
  if (in_place.empty()) return InClassScope(type, decl, scope);
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = in_place;
  return named;
}

static uint32_t SizedParamWidth(const DataType& type, const ClassDecl& decl,
                                const ScopeMap& scope, SimContext& ctx) {
  uint32_t width = OuterParamPartsWidth(type, decl, ctx);
  return width != 0 ? width : SimParamTypeWidth(type, scope, ctx);
}

Logic4Vec ClassParamSizer::Value(std::string_view name, const DataType* type,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  DataType scoped;
  if (type != nullptr && type->kind == DataTypeKind::kNamed &&
      type->scope_name.empty() && type->packed_dim_left == nullptr) {
    if (const DataType* bound = TypeParamType(type->type_name)) type = bound;
  }
  if (type != nullptr)
    scoped =
        SizedParamType(name, *type, *decl_,
                       type_scope_.empty() ? decl_->name : type_scope_, ctx);
  bool is_real = type != nullptr && DeclaredTypeIsReal(scoped, ctx);
  uint32_t width = type != nullptr && !is_real
                       ? SizedParamWidth(scoped, *decl_, scope_, ctx)
                       : 0;
  Logic4Vec val = ParamValueOfType(scoped, expr, width, ctx, arena);
  if (width != 0 && !DeclaredTypeIs4State(scoped, ctx)) CoerceTo2State(val);
  if (is_real) val = ToDeclaredReal(val, &scoped, ctx, arena);
  if (!name.empty() && !val.is_real)
    scope_[name] = static_cast<int64_t>(val.ToUint64());
  return val;
}

const DataType* ClassParamSizer::TypeParamType(std::string_view name) const {
  if (decl_ == nullptr || decl_->type_param_names.count(name) == 0)
    return nullptr;
  for (size_t i = 0; i < decl_->params.size(); ++i) {
    if (decl_->params[i].first != name) continue;
    const DataType* actual = type_actuals_ == nullptr
                                 ? nullptr
                                 : ActualForParam(*type_actuals_, i, name);
    if (actual == nullptr && i < decl_->param_types.size())
      actual = &decl_->param_types[i];
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit)
      return nullptr;
    return actual;
  }
  return nullptr;
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

static bool IsDollarValue(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kIdentifier && e->text == "$";
}

static void MarkIfUnbounded(ClassObject* obj, std::string_view pname,
                            const Expr* value, bool names_unbounded) {
  bool unbounded = IsDollarValue(value) ||
                   (value != nullptr && value->kind == ExprKind::kIdentifier &&
                    names_unbounded);
  if (unbounded) {
    obj->unbounded_params.insert(std::string(pname));
  } else {
    obj->unbounded_params.erase(std::string(pname));
  }
}

static bool NamesMarkedParam(const ClassObject* obj, const Expr* value) {
  return value != nullptr &&
         obj->unbounded_params.count(std::string(value->text)) != 0;
}

static void MarkUnboundedBodyParams(ClassObject* obj, const ClassDecl* decl) {
  for (const auto* m : decl->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_param) continue;
    MarkIfUnbounded(obj, m->name, m->init_expr,
                    NamesMarkedParam(obj, m->init_expr));
  }
}

void MarkUnboundedClassParams(ClassObject* obj, const ClassDecl* decl) {
  for (const auto& [pname, pexpr] : decl->params) {
    MarkIfUnbounded(obj, pname, pexpr, NamesMarkedParam(obj, pexpr));
  }
  MarkUnboundedBodyParams(obj, decl);
}

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const std::vector<DataType>* actuals =
      ctx.FindVariableClassTypeParams(var_name);
  if (actuals == nullptr) actuals = obj->type->param_actuals;
  BindTypeParamActuals(obj, actuals);
  if (actuals == nullptr) return;
  const auto& params = obj->type->decl->params;
  ClassParamSizer sizer(obj->type->decl);
  sizer.UseTypeActuals(actuals);
  for (size_t i = 0; i < params.size(); ++i) {
    const DataType* actual = ActualForParam(*actuals, i, params[i].first);
    if (actual == nullptr || actual->type_ref_expr == nullptr) {
      auto kept = obj->properties.find(std::string(params[i].first));
      if (kept != obj->properties.end()) sizer.Record(i, kept->second);
      MarkIfUnbounded(obj, params[i].first, params[i].second,
                      NamesMarkedParam(obj, params[i].second));
      continue;
    }
    const Expr* written = actual->type_ref_expr;
    MarkIfUnbounded(obj, params[i].first, written,
                    ctx.IsUnboundedParam(written->text));
    auto val = OwnRhsWords(sizer.Value(i, written, ctx, arena), arena);
    obj->properties[std::string(params[i].first)] = val;
    std::string scoped =
        std::string(obj->type->name) + "::" + std::string(params[i].first);
    obj->properties[scoped] = val;
  }
  MarkUnboundedBodyParams(obj, obj->type->decl);
  std::string_view cls = obj->type->name;
  ClassParamSizer body_sizer(obj->type->decl);
  body_sizer.UseTypeActuals(actuals);
  ClassParamStorage storage{
      [obj](std::string_view name) -> const Logic4Vec* {
        auto it = obj->properties.find(std::string(name));
        return it != obj->properties.end() ? &it->second : nullptr;
      },
      [obj, cls](std::string_view name, const Logic4Vec& value) {
        obj->properties[std::string(name)] = value;
        obj->properties[std::string(cls) + "::" + std::string(name)] = value;
      }};
  FoldClassBodyParams(body_sizer, storage, ctx, arena);
}

ClassParamStorage ClassStaticStorage(ClassTypeInfo* info) {
  return {[info](std::string_view name) -> const Logic4Vec* {
            auto it = info->static_properties.find(std::string(name));
            return it != info->static_properties.end() ? &it->second : nullptr;
          },
          [info](std::string_view name, const Logic4Vec& value) {
            info->static_properties[std::string(name)] = value;
          },
          info};
}

static bool IsPartRead(const Expr* e) {
  return e->kind == ExprKind::kSelect ||
         (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution);
}

static const Expr* PartReadRoot(const Expr* e) {
  while (IsPartRead(e)) e = e->kind == ExprKind::kSelect ? e->base : e->lhs;
  return e;
}

static bool IsOwnParam(const ClassDecl& decl, std::string_view name) {
  return std::ranges::any_of(
             decl.params, [name](const auto& p) { return p.first == name; }) ||
         std::ranges::any_of(decl.members, [name](const ClassMember* m) {
           return m->is_param && m->name == name;
         });
}

static bool ReadsParamPart(const Expr* e, const ClassDecl& decl, bool own) {
  if (e == nullptr) return false;
  if (IsPartRead(e)) {
    const Expr* root = PartReadRoot(e);
    bool is_own = root->kind == ExprKind::kIdentifier &&
                  root->scope_prefix.empty() && IsOwnParam(decl, root->text);
    return is_own == own;
  }
  return ReadsParamPart(e->lhs, decl, own) || ReadsParamPart(e->rhs, decl, own);
}

static bool PackedDimsReadParamParts(const DataType& type,
                                     const ClassDecl& decl, bool own) {
  std::vector<const Expr*> bounds{type.packed_dim_left, type.packed_dim_right};
  for (const auto& [left, right] : type.extra_packed_dims) {
    bounds.push_back(left);
    bounds.push_back(right);
  }
  return std::ranges::any_of(bounds, [&decl, own](const Expr* bound) {
    return ReadsParamPart(bound, decl, own);
  });
}

uint32_t OuterParamPartsWidth(const DataType& type, const ClassDecl& decl,
                              SimContext& ctx) {
  return PackedDimsReadParamParts(type, decl, false)
             ? RunningDimsWidth(type, ctx)
             : 0;
}

static uint32_t WidthReadingParamParts(const ClassMember& m,
                                       const ClassDecl& decl, SimContext& ctx) {
  if (m.kind != ClassMemberKind::kProperty || m.is_param ||
      !m.unpacked_dims.empty() ||
      !PackedDimsReadParamParts(m.data_type, decl, true))
    return 0;
  return DeclaredTypeWidth(m.data_type, ctx);
}

static void ResizeProperty(ClassTypeInfo& info, std::string_view name,
                           uint32_t width, Arena& arena) {
  for (auto& prop : info.properties) {
    if (prop.name != name) continue;
    prop.width = width;
    if (prop.is_static)
      info.static_properties[std::string(prop.name)] =
          prop.is_4state ? MakeAllX(arena, width)
                         : MakeLogic4VecVal(arena, width, 0);
  }
}

static void SizePropertiesReadingParamParts(ClassTypeInfo* info,
                                            SimContext& ctx, Arena& arena) {
  for (const auto* m : info->decl->members) {
    uint32_t width = WidthReadingParamParts(*m, *info->decl, ctx);
    if (width != 0) ResizeProperty(*info, m->name, width, arena);
  }
}

static ArrayInfo ParamArrayShape(const ClassTypeInfo::PropertyInfo& prop) {
  ArrayInfo shape;
  shape.lo = static_cast<uint32_t>(prop.array_lo);
  shape.size = prop.array_size;
  shape.is_descending = prop.array_descending;
  shape.elem_width = prop.width;
  shape.is_4state = prop.is_4state;
  shape.dim_los = prop.dim_los;
  shape.dim_sizes = prop.dim_sizes;
  shape.dim_descending = prop.dim_descending;
  return shape;
}

static void FillParamArrayLocal(std::string_view name, const ArrayInfo& shape,
                                const Expr* init, SimContext& ctx,
                                Arena& arena) {
  const ArrayInfo* source = init->kind == ExprKind::kIdentifier
                                ? ctx.FindArrayInfo(init->text)
                                : nullptr;
  if (source != nullptr) {
    CopyArrayElements(name, shape, init->text, *source, ctx);
    return;
  }
  DistributePatternToArray(name, shape, UnwrapTypedPattern(init), ctx, arena);
}

static void BindParamArrayLocal(std::string_view name, const DataType* type,
                                const ClassTypeInfo::PropertyInfo& prop,
                                SimContext& ctx, Arena& arena) {
  const ArrayInfo kShape = ParamArrayShape(prop);
  ctx.RegisterLocalArray(name, kShape);
  std::vector<Variable*> leaves;
  for (uint32_t k = 0; k < ArrayElementCount(kShape); ++k) {
    auto* key = arena.Create<std::string>(std::string(name) +
                                          ArrayElementSuffixAt(kShape, k));
    leaves.push_back(ctx.CreateLocalVariable(*key, kShape.elem_width));
  }
  FillParamArrayLocal(name, kShape, prop.init_expr, ctx, arena);
  for (Variable* leaf : leaves) ShapeParamLocal(type, leaf, ctx, arena);
}

namespace {

struct BoundParam {
  std::string_view name;
  const DataType* type = nullptr;
  bool unpacked = false;
};

}  // namespace

static void BindParamLocal(const BoundParam& param, const Logic4Vec& value,
                           const ClassTypeInfo* sized, SimContext& ctx,
                           Arena& arena) {
  const ClassTypeInfo::PropertyInfo* prop =
      param.unpacked && sized != nullptr ? sized->FindProperty(param.name)
                                         : nullptr;
  if (prop != nullptr) {
    BindParamArrayLocal(param.name, param.type, *prop, ctx, arena);
    return;
  }
  Variable* local = ctx.CreateLocalVariable(param.name, value.width);
  local->value = value;
  ShapeParamLocal(param.type, local, ctx, arena);
}

void FoldClassBodyParams(ClassParamSizer sizer,
                         const ClassParamStorage& storage, SimContext& ctx,
                         Arena& arena) {
  const ClassDecl* decl = sizer.Decl();
  ctx.PushScope();
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) != 0) continue;
    const Logic4Vec* value = storage.header(pname);
    if (value == nullptr) continue;
    BindParamLocal({pname, ParamType(decl, i),
                    decl->param_port_unpacked_dims.count(pname) != 0},
                   *value, storage.sized, ctx, arena);
  }
  for (const auto* m : decl->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_param ||
        m->init_expr == nullptr || m->data_type.kind == DataTypeKind::kVoid)
      continue;
    Logic4Vec value = OwnRhsWords(
        sizer.Value(m->name, &m->data_type, m->init_expr, ctx, arena), arena);
    storage.store(m->name, value);
    BindParamLocal({m->name, &m->data_type, !m->unpacked_dims.empty()}, value,
                   storage.sized, ctx, arena);
  }
  if (storage.sized != nullptr)
    SizePropertiesReadingParamParts(storage.sized, ctx, arena);
  ctx.PopScope();
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

static void AddNamedTypedefs(const DataType& type, const SimContext& ctx,
                             TypedefMap& types) {
  const DataType* named = &type;
  while (named->kind == DataTypeKind::kNamed &&
         types.count(named->type_name) == 0) {
    const ModuleItem* item = ctx.FindTypedefItem(named->type_name);
    if (item == nullptr) return;
    types.emplace(named->type_name, item->typedef_type);
    named = &item->typedef_type;
  }
}

TypedefMap TypeParamTypes(const ClassDecl* decl,
                          const std::vector<DataType>& actuals,
                          const SimContext& ctx) {
  TypedefMap types;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* type = ActualForParam(actuals, i, pname);
    if (type == nullptr && i < decl->param_types.size())
      type = &decl->param_types[i];
    if (type == nullptr || type->kind == DataTypeKind::kImplicit) continue;
    types.emplace(pname, *type);
    AddNamedTypedefs(*type, ctx, types);
  }
  return types;
}

}  // namespace delta
