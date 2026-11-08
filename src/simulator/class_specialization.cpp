#include "simulator/class_specialization.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization_key.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

std::vector<DataType> ScopeActuals(const Expr& base) {
  std::vector<DataType> actuals(base.elements.size());
  for (size_t i = 0; i < base.elements.size(); ++i) {
    actuals[i].type_ref_expr = base.elements[i];
    if (i < base.arg_names.size())
      actuals[i].param_arg_name = base.arg_names[i];
  }
  return actuals;
}

const DataType* BaseActual(const ClassDecl* decl,
                           const std::vector<DataType>& actuals) {
  if (decl->base_class.empty() ||
      decl->type_param_names.count(decl->base_class) == 0) {
    return nullptr;
  }
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == decl->base_class)
      return ActualForParam(actuals, i, decl->base_class);
  }
  return nullptr;
}

const DataType* HolderActualFor(const ClassTypeInfo* holder,
                                std::string_view pname) {
  if (holder->param_actuals == nullptr) return nullptr;
  const ClassDecl* decl = holder->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == pname)
      return ActualForParam(*holder->param_actuals, i, pname);
  }
  return nullptr;
}

const ClassTypeInfo* HolderScopeClass(const ClassTypeInfo* holder,
                                      const DataType& actual, SimContext& ctx) {
  if (!actual.type_params.empty() || !actual.scope_name.empty()) return nullptr;
  for (const ClassTypeInfo* level = holder; level != nullptr;
       level = level->parent) {
    if (const ClassTypeInfo* cls = ctx.FindClassType(
            std::string(level->name) + "::" + std::string(actual.type_name)))
      return cls;
  }
  return nullptr;
}

void QualifyHolderTypedef(const ClassTypeInfo* holder, DataType& actual) {
  if (!actual.type_params.empty() || !actual.scope_name.empty()) return;
  if (ClassScopeTypedefItem(holder, actual.type_name) == nullptr) return;
  actual.scope_name = holder->name;
}

std::string_view GenericNameOf(std::string_view name) {
  return name.substr(0, name.find("#("));
}

ClassTypeInfo* BaseUnderOwnParams(const ClassTypeInfo* info,
                                  ClassTypeInfo* base, SimContext& ctx,
                                  Arena& arena) {
  const ClassDecl* decl = info->decl;
  if (!info->package.empty()) ctx.PushScope(info->package);
  ctx.PushScope();
  for (const auto& [pname, pexpr] : decl->params) {
    if (decl->type_param_names.count(pname) != 0) continue;
    auto entry = info->static_properties.find(std::string(pname));
    if (entry == info->static_properties.end()) continue;
    ctx.CreateLocalVariable(pname, entry->second.width)->value = entry->second;
  }
  ClassTypeInfo* spec = SpecializationOf(
      base, ActualsUnderSpecialization(info, decl->base_class_type_params, ctx),
      ctx, arena);
  ctx.PopScope();
  if (!info->package.empty()) ctx.PopScope();
  return spec;
}

void BindSpecializationBase(ClassTypeInfo* spec,
                            const std::vector<DataType>& actuals,
                            SimContext& ctx, Arena& arena) {
  const ClassDecl* decl = spec->decl;
  if (!decl->base_class_type_params.empty() &&
      decl->type_param_names.count(decl->base_class) == 0) {
    ClassTypeInfo* base =
        spec->parent != nullptr
            ? ctx.FindClassType(GenericNameOf(spec->parent->name))
            : nullptr;
    if (base == nullptr) return;
    spec->parent = BaseUnderOwnParams(spec, base, ctx, arena);
    return;
  }
  const DataType* actual = BaseActual(decl, actuals);
  if (actual == nullptr || actual->kind != DataTypeKind::kNamed) return;
  if (ClassTypeInfo* base = ctx.FindClassType(actual->type_name))
    spec->parent = base;
}

std::vector<DataType> SpelledActuals(const ClassDecl* decl,
                                     const std::vector<DataType>& actuals) {
  std::vector<DataType> spelled = actuals;
  for (size_t j = 0; j < spelled.size(); ++j) {
    DataType& actual = spelled[j];
    std::string_view pname = actual.param_arg_name;
    if (pname.empty() && j < decl->params.size()) pname = decl->params[j].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    if (actual.kind != DataTypeKind::kImplicit ||
        actual.type_ref_expr == nullptr) {
      continue;
    }
    DataType type = TypeSpelledBy(actual.type_ref_expr);
    if (type.kind == DataTypeKind::kImplicit) continue;
    type.param_arg_name = actual.param_arg_name;
    actual = type;
  }
  return spelled;
}

}  // namespace

const DataType* RunningTypeActual(std::string_view name, SimContext& ctx) {
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  if (running == nullptr || running->decl == nullptr ||
      running->decl->type_param_names.count(name) == 0) {
    return nullptr;
  }
  if (const DataType* bound = ctx.FindScopeTypeActual(name)) return bound;
  if (const DataType* actual = HolderActualFor(running, name)) return actual;
  const ClassObject* self = ctx.CurrentThis();
  bool own = self != nullptr && self->type != nullptr &&
             self->type->decl == running->decl;
  return TypeParamActual(own ? self : nullptr, running->decl, name);
}

namespace {

std::vector<DataType> ActualsUnderRunningClass(
    const ClassDecl* decl, const std::vector<DataType>& written,
    SimContext& ctx) {
  std::vector<DataType> bound = SpelledActuals(decl, written);
  for (DataType& actual : bound) {
    if (actual.kind != DataTypeKind::kNamed) continue;
    const DataType* a = RunningTypeActual(actual.type_name, ctx);
    if (a == nullptr) continue;
    std::string_view arg = actual.param_arg_name;
    actual = *a;
    actual.param_arg_name = arg;
  }
  return bound;
}

}  // namespace

std::vector<DataType> ActualsUnderSpecialization(
    const ClassTypeInfo* holder, const std::vector<DataType>& written,
    SimContext& ctx) {
  std::vector<DataType> bound = written;
  for (DataType& actual : bound) {
    if (actual.kind != DataTypeKind::kNamed) continue;
    if (holder->decl->type_param_names.count(actual.type_name) == 0) {
      if (const ClassTypeInfo* cls = HolderScopeClass(holder, actual, ctx))
        actual.type_name = cls->name;
      else
        QualifyHolderTypedef(holder, actual);
      continue;
    }
    const DataType* a = HolderActualFor(holder, actual.type_name);
    if (a == nullptr && holder->param_actuals == nullptr)
      a = TypeParamActual(nullptr, holder->decl, actual.type_name);
    if (a == nullptr) continue;
    std::string_view arg = actual.param_arg_name;
    actual = *a;
    actual.param_arg_name = arg;
  }
  return bound;
}

ClassTypeInfo* ClassNamedByTypeParam(std::string_view name, SimContext& ctx,
                                     Arena& arena) {
  const DataType* actual = RunningTypeActual(name, ctx);
  if (actual == nullptr || actual->kind != DataTypeKind::kNamed) return nullptr;
  ClassTypeInfo* generic = nullptr;
  if (!actual->scope_name.empty()) {
    generic = ctx.FindClassType(std::string(actual->scope_name) +
                                "::" + std::string(actual->type_name));
  }
  if (generic == nullptr) generic = ctx.FindClassType(actual->type_name);
  if (generic == nullptr) return nullptr;
  return SpecializationOf(generic, actual->type_params, ctx, arena);
}

namespace {

using ParamValues = std::vector<std::pair<std::string_view, Logic4Vec>>;

std::string SpecializationKey(const ClassTypeInfo* generic,
                              const std::vector<DataType>& spelled,
                              SimContext& ctx, Arena& arena,
                              ParamValues& values) {
  const ClassDecl* decl = generic->decl;
  ClassParamSizer sizer(decl);
  sizer.UseTypeActuals(&spelled);
  std::string key(generic->name);
  key += "#(";
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (i != 0) key += ",";
    std::string_view pname = decl->params[i].first;
    const DataType* actual = ActualForParam(spelled, i, pname);
    if (decl->type_param_names.count(pname) != 0) {
      key += TypeActualKey(decl, i, actual, ctx);
      continue;
    }
    const Expr* expr = actual != nullptr && actual->type_ref_expr != nullptr
                           ? actual->type_ref_expr
                           : decl->params[i].second;
    Logic4Vec value = expr != nullptr ? sizer.Value(i, expr, ctx, arena)
                                      : MakeLogic4VecVal(arena, 32, 0);
    key += std::to_string(value.ToUint64());
    values.emplace_back(pname, value);
  }
  key += ")";
  return key;
}

void OwnVTableEntries(ClassTypeInfo* spec) {
  for (VTableEntry& entry : spec->vtable) {
    if (entry.owner == nullptr) continue;
    for (const ClassTypeInfo* level = spec; level != nullptr;
         level = level->parent) {
      if (level->decl == entry.owner->decl) {
        entry.owner = level;
        break;
      }
    }
  }
}

const DataType* TypeParamActualIn(const ClassDecl* decl,
                                  const std::vector<DataType>& actuals,
                                  std::string_view name) {
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == name) return ActualForParam(actuals, i, name);
  }
  return nullptr;
}

bool ActualSizesIntegralProperty(const DataType& actual, SimContext& ctx) {
  if (DeclaredTypeIsString(actual, ctx) || DeclaredTypeIsReal(actual, ctx))
    return false;
  if (actual.kind != DataTypeKind::kNamed) return true;
  const ModuleItem* item = ctx.FindTypedefItem(actual.type_name);
  return item == nullptr || item->unpacked_dims.empty();
}

void SizeTypeParamProperties(ClassTypeInfo* spec,
                             const std::vector<DataType>& actuals,
                             SimContext& ctx) {
  const ClassDecl* decl = spec->decl;
  for (auto& prop : spec->properties) {
    std::string_view pname = prop.type_name.empty()
                                 ? std::string_view{}
                                 : TypeParamNamedBy(decl, prop.type_name);
    if (prop.width_is_declared || pname.empty()) continue;
    const DataType* actual = TypeParamActualIn(decl, actuals, pname);
    if (actual == nullptr || !ActualSizesIntegralProperty(*actual, ctx))
      continue;
    uint32_t width = DeclaredTypeWidth(*actual, ctx);
    if (width == 0) continue;
    prop.width = width;
    prop.width_is_declared = true;
    prop.is_signed = DeclaredTypeIsSigned(*actual, ctx);
    if (actual->kind != DataTypeKind::kNamed)
      prop.is_4state = DeclaredTypeIs4State(*actual, ctx);
  }
}

const ClassMember* DeclaredProperty(const ClassDecl* decl,
                                    std::string_view name) {
  for (const auto* m : decl->members) {
    if (m->kind == ClassMemberKind::kProperty && !m->is_param &&
        m->name == name)
      return m;
  }
  return nullptr;
}

ScopeMap SpecializationParamScope(const ClassTypeInfo* spec,
                                  const ParamValues& values) {
  ScopeMap scope;
  if (spec->unit_constants != nullptr) scope = *spec->unit_constants;
  for (const auto& [pname, value] : values)
    scope[pname] = SelectBoundValue(value);
  for (const auto* member : spec->decl->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param ||
        member->init_expr == nullptr) {
      continue;
    }
    if (auto v = ConstEvalInt(member->init_expr, scope))
      scope[member->name] = *v;
  }
  return scope;
}

bool SizeClassTypedefProperty(ClassTypeInfo::PropertyInfo& prop,
                              const DataType& type, const ClassTypeInfo* spec,
                              const ScopeMap& scope, SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return false;
  if (ClassAggregateTypedef(*spec->decl, type.type_name) == nullptr)
    return false;
  std::string_view key = RegisterSpecializationTypedefLayout(
      spec->name, *spec, type.type_name, scope, ctx);
  if (const StructTypeInfo* layout = ctx.FindStructType(key)) {
    prop.type_name = key;
    prop.width = layout->total_width;
    prop.width_is_declared = true;
  }
  return true;
}

std::string_view BaseTypedefKey(const DataType& type, const ClassTypeInfo& spec,
                                SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) return {};
  const ClassDecl* decl = nullptr;
  const ClassTypeInfo* owner =
      ClassTypedefDeclarer(type.type_name, spec, *spec.decl, decl);
  if (owner == nullptr || owner == &spec || !ClassHasValueParams(*decl))
    return {};
  if (ClassAggregateTypedef(*decl, type.type_name) == nullptr) return {};
  return ClassTypedefLayoutKey(*owner, type.type_name, ctx);
}

void SizeBaseTypedefProperties(ClassTypeInfo* spec, SimContext& ctx) {
  for (auto& prop : spec->properties) {
    const ClassMember* member = DeclaredProperty(spec->decl, prop.name);
    if (member == nullptr) continue;
    std::string_view key = BaseTypedefKey(member->data_type, *spec, ctx);
    const StructTypeInfo* layout =
        key.empty() ? nullptr : ctx.FindStructType(key);
    if (layout == nullptr) continue;
    prop.type_name = key;
    prop.width = layout->total_width;
    prop.width_is_declared = true;
  }
}

void RefoldPropertyArraySize(ClassTypeInfo::PropertyInfo& prop,
                             const ClassMember& member, const ScopeMap& scope,
                             SimContext& ctx, Arena& arena) {
  if (prop.array_size == 0 || member.unpacked_dims.size() != 1) return;
  PropertyArrayDim dim =
      FoldPropertyDimension(member.unpacked_dims[0], scope, ctx, arena);
  if (dim.size > 0) prop.array_size = dim.size;
}

void SizeValueParamProperties(ClassTypeInfo* spec, const ParamValues& values,
                              const std::vector<DataType>& actuals,
                              SimContext& ctx, Arena& arena) {
  if (values.empty() && actuals.empty()) return;
  ScopeMap scope = SpecializationParamScope(spec, values);
  TypedefMap type_params = TypeParamTypes(spec->decl, actuals, ctx);
  TypedefRegistryGuard type_param_guard(&type_params, nullptr);
  for (auto& prop : spec->properties) {
    const ClassMember* member = DeclaredProperty(spec->decl, prop.name);
    if (member == nullptr) continue;
    RefoldPropertyArraySize(prop, *member, scope, ctx, arena);
    const DataType& type = *TypeOfThisNamed(&member->data_type, spec, ctx);
    if (SizeClassTypedefProperty(prop, type, spec, scope, ctx)) continue;
    uint32_t width = EvalTypeWidth(type, {}, scope);
    if (width == 0)
      width = DeclaredTypeWidth(
          ClassPropertyType(type, spec->decl, type_params), ctx);
    if (width == 0) continue;
    prop.width = width;
    prop.width_is_declared = true;
  }
}

}  // namespace

static std::optional<int64_t> RunningScopeSize(const Expr* dim, SimContext& ctx,
                                               Arena& arena) {
  bool readable = dim->kind == ExprKind::kIdentifier
                      ? ctx.FindVariable(dim->text) != nullptr
                      : dim->kind == ExprKind::kBinary;
  if (!readable) return std::nullopt;
  Logic4Vec value = EvalExpr(dim, ctx, arena);
  if (!value.IsKnown()) return std::nullopt;
  return static_cast<int64_t>(value.ToUint64());
}

PropertyArrayDim FoldPropertyDimension(const Expr* dim, const ScopeMap& scope,
                                       SimContext& ctx, Arena& arena) {
  if (dim == nullptr) return {};
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon ||
      dim->lhs == nullptr || dim->rhs == nullptr) {
    std::optional<int64_t> size = ConstEvalInt(dim, scope);
    if (!size) size = RunningScopeSize(dim, ctx, arena);
    if (!size || *size <= 0) return {};
    return {static_cast<uint32_t>(*size), 0, false};
  }
  auto bound = [&](const Expr* e) {
    if (auto v = ConstEvalInt(e, scope)) return *v;
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  int64_t left = bound(dim->lhs);
  int64_t right = bound(dim->rhs);
  if (left < right) {
    return {static_cast<uint32_t>(right - left + 1), left, false};
  }
  return {static_cast<uint32_t>(left - right + 1), right, left > right};
}

static void TakeParamArrayActuals(ClassTypeInfo* spec,
                                  const std::vector<DataType>& spelled) {
  const ClassDecl* decl = spec->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->param_port_unpacked_dims.count(pname) == 0) continue;
    const DataType* actual = ActualForParam(spelled, i, pname);
    if (actual == nullptr) continue;
    for (auto& prop : spec->properties) {
      if (prop.name == pname) prop.init_expr = actual->type_ref_expr;
    }
  }
}

namespace {

struct MadeActuals {
  const std::vector<DataType>* spelled = nullptr;
  const ParamValues* values = nullptr;
};

}  // namespace

static ClassTypeInfo* MakeSpecialization(ClassTypeInfo* generic,
                                         std::string key,
                                         const MadeActuals& made,
                                         SimContext& ctx, Arena& arena) {
  const std::vector<DataType>& spelled = *made.spelled;
  const ParamValues& values = *made.values;
  auto* spec = arena.Create<ClassTypeInfo>(*generic);
  spec->name = *arena.Create<std::string>(std::move(key));
  spec->param_actuals = arena.Create<std::vector<DataType>>(spelled);
  SizeTypeParamProperties(spec, spelled, ctx);
  SizeValueParamProperties(spec, values, spelled, ctx, arena);
  TakeParamArrayActuals(spec, spelled);
  for (auto& [pname, value] : values)
    spec->static_properties[std::string(pname)] = value;
  BindSpecializationBase(spec, spelled, ctx, arena);
  SizeBaseTypedefProperties(spec, ctx);
  OwnVTableEntries(spec);
  ClassParamSizer body_sizer(generic->decl, generic->name);
  body_sizer.UseTypeActuals(spec->param_actuals);
  FoldClassBodyParams(body_sizer, ClassStaticLookup(spec),
                      ClassStaticStore(spec), ctx, arena);
  ctx.RegisterClassType(spec->name, spec);
  RegisterClassScopeTypedefAliases(spec, ctx, arena);
  InitSpecializationStaticProperties(spec, ctx, arena);
  return spec;
}

ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena) {
  if (generic == nullptr || generic->decl == nullptr || actuals.empty())
    return generic;
  std::vector<DataType> spelled = SpelledActuals(generic->decl, actuals);
  ParamValues values;
  std::string key = SpecializationKey(generic, spelled, ctx, arena, values);
  ParamValues default_values;
  if (key == SpecializationKey(generic, {}, ctx, arena, default_values))
    return generic;
  const std::string kOuter =
      ctx.SetClassInstanceScope(std::string(generic->instance_scope));
  ClassTypeInfo* spec = generic->instance_scope.empty()
                            ? ctx.FindClassType(key)
                            : ctx.ExactClassType(key);
  if (spec == nullptr) {
    spec = MakeSpecialization(generic, std::move(key), {&spelled, &values}, ctx,
                              arena);
  }
  ctx.SetClassInstanceScope(kOuter);
  return spec;
}

void BindDeclarationBase(ClassTypeInfo* info, SimContext& ctx, Arena& arena) {
  const ClassDecl* decl = info->decl;
  if (decl == nullptr || info->parent == nullptr ||
      decl->base_class_type_params.empty() ||
      decl->type_param_names.count(decl->base_class) != 0) {
    return;
  }
  ClassTypeInfo* base = ctx.FindClassType(info->parent->name);
  if (base == nullptr) return;
  ClassTypeInfo* spec = BaseUnderOwnParams(info, base, ctx, arena);
  if (spec == nullptr || spec == base) return;
  info->parent = spec;
  OwnVTableEntries(info);
  SizeBaseTypedefProperties(info, ctx);
}

ClassTypeInfo* ScopeNamedSpecialization(const Expr* base, SimContext& ctx,
                                        Arena& arena) {
  ClassTypeInfo* generic = ctx.FindClassType(ScopedClassKey(base, arena));
  if (generic == nullptr || generic->decl == nullptr) return nullptr;
  if (base->has_param_spec && !base->elements.empty()) {
    return SpecializationOf(
        generic,
        ActualsUnderRunningClass(generic->decl, ScopeActuals(*base), ctx), ctx,
        arena);
  }
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  if (running == nullptr || running->decl != generic->decl) return nullptr;
  return ctx.FindClassType(running->name);
}

bool TryScopeSpecializationStaticMember(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ClassTypeInfo* spec = ScopeNamedSpecialization(expr->lhs, ctx, arena);
  if (spec == nullptr) return false;
  const ClassTypeInfo* declarer = spec->StaticPropertyDeclarer(expr->rhs->text);
  if (declarer == nullptr) return false;
  out = declarer->static_properties.find(std::string(expr->rhs->text))->second;
  return true;
}

}  // namespace delta
