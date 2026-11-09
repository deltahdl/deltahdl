#include "simulator/class_typedef_layout.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_params.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

ScopeMap ParamValuesOf(const ClassTypeInfo& cls) {
  ScopeMap scope;
  if (cls.unit_constants != nullptr) scope = *cls.unit_constants;
  auto bind = [&](std::string_view name) {
    auto it = cls.static_properties.find(std::string(name));
    if (it != cls.static_properties.end())
      scope[name] = SelectBoundValue(it->second);
  };
  for (const auto& param : cls.decl->params) bind(param.first);
  for (const auto* member : cls.decl->members) {
    if (member->kind == ClassMemberKind::kProperty && member->is_param)
      bind(member->name);
  }
  return scope;
}

std::optional<uint32_t> FoldedPackedWidth(const StructMember& m,
                                          const ScopeMap& scope) {
  if (m.packed_dim_left == nullptr || m.packed_dim_right == nullptr)
    return std::nullopt;
  auto span = [&](const Expr* l, const Expr* r) -> std::optional<uint32_t> {
    auto lv = ConstEvalInt(l, scope);
    auto rv = ConstEvalInt(r, scope);
    if (!lv || !rv) return std::nullopt;
    return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  };
  std::optional<uint32_t> width = span(m.packed_dim_left, m.packed_dim_right);
  for (const auto& [l, r] : m.extra_packed_dims) {
    std::optional<uint32_t> dim = span(l, r);
    if (!width || !dim) return std::nullopt;
    *width *= *dim;
  }
  return width;
}

std::optional<uint32_t> ClassTypedefMemberWidth(const StructMember& m,
                                                const ScopeMap& scope,
                                                const ClassTypeInfo& declarer,
                                                const SimContext& ctx) {
  if (!m.scope_name.empty()) return std::nullopt;
  const ClassDecl* decl = nullptr;
  const ClassTypeInfo* owner =
      ClassTypedefDeclarer(m.type_name, declarer, *declarer.decl, decl);
  if (owner == nullptr) return std::nullopt;
  const auto kTypedef =
      std::find_if(decl->members.begin(), decl->members.end(),
                   [&](const ClassMember* member) {
                     return member->kind == ClassMemberKind::kTypedef &&
                            member->name == m.type_name;
                   });
  const ScopeMap kOwnerScope =
      owner == &declarer ? scope : ParamValuesOf(*owner);
  return SimParamTypeWidth((*kTypedef)->typedef_item->typedef_type, kOwnerScope,
                           ctx) *
         FoldedPackedWidth(m, scope).value_or(1);
}

uint32_t FoldedMemberWidth(const StructMember& m, const ScopeMap& scope,
                           const ClassTypeInfo& declarer,
                           const SimContext& ctx) {
  if (m.type_kind != DataTypeKind::kNamed)
    return FoldedPackedWidth(m, scope).value_or(0);
  if (auto width = ClassTypedefMemberWidth(m, scope, declarer, ctx))
    return *width;
  DataType written;
  written.kind = m.type_kind;
  written.type_name = m.type_name;
  written.scope_name = m.scope_name;
  written.packed_dim_left = m.packed_dim_left;
  written.packed_dim_right = m.packed_dim_right;
  written.extra_packed_dims = m.extra_packed_dims;
  return SimParamTypeWidth(written, scope, ctx);
}

DataType* FoldedAggregate(const DataType& type, const ScopeMap& scope,
                          const ClassTypeInfo& declarer, SimContext& ctx) {
  auto* folded = ctx.GetArena().Create<DataType>(type);
  for (StructMember& m : folded->struct_members) {
    if (m.nested_type != nullptr) continue;
    if (uint32_t width = FoldedMemberWidth(m, scope, declarer, ctx))
      m.resolved_width = width;
  }
  return folded;
}

}  // namespace

bool ClassHasValueParams(const ClassDecl& decl) {
  if (!decl.params.empty()) return true;
  for (const auto* member : decl.members) {
    if (member->kind == ClassMemberKind::kProperty && member->is_param)
      return true;
  }
  return false;
}

const DataType* ClassAggregateTypedef(const ClassDecl& decl,
                                      std::string_view name) {
  for (const auto* member : decl.members) {
    if (member->kind != ClassMemberKind::kTypedef ||
        member->typedef_item == nullptr || member->name != name) {
      continue;
    }
    const DataType& type = member->typedef_item->typedef_type;
    bool aggregate = (type.kind == DataTypeKind::kStruct ||
                      type.kind == DataTypeKind::kUnion) &&
                     !type.struct_members.empty();
    return aggregate ? &type : nullptr;
  }
  return nullptr;
}

std::string_view RegisterSpecializationTypedefLayout(
    std::string_view spelled, const ClassTypeInfo& declarer,
    std::string_view name, const ScopeMap& scope, SimContext& ctx) {
  auto* key = ctx.GetArena().Create<std::string>(std::string(spelled) +
                                                 "::" + std::string(name));
  if (ctx.FindStructType(*key) == nullptr) {
    const DataType* type = ClassAggregateTypedef(*declarer.decl, name);
    RegisterTypeLayout(*key, FoldedAggregate(*type, scope, declarer, ctx), ctx,
                       ctx.GetArena());
  }
  return *key;
}

const ClassTypeInfo* ClassTypedefDeclarer(std::string_view name,
                                          const ClassTypeInfo& info,
                                          const ClassDecl& cls,
                                          const ClassDecl*& decl) {
  decl = &cls;
  for (const ClassTypeInfo* c = &info; c != nullptr && decl != nullptr;) {
    for (const auto* member : decl->members) {
      if (member->kind == ClassMemberKind::kTypedef && member->name == name)
        return c;
    }
    c = c->parent;
    decl = c != nullptr ? c->decl : nullptr;
  }
  return nullptr;
}

std::string_view ClassTypedefLayoutKey(const ClassTypeInfo& cls,
                                       std::string_view name, SimContext& ctx) {
  std::string spelled = std::string(cls.name);
  if (cls.param_actuals == nullptr) spelled += "#()";
  return RegisterSpecializationTypedefLayout(spelled, cls, name,
                                             ParamValuesOf(cls), ctx);
}

std::string_view InPlaceAggregateLayoutKey(std::string_view scope,
                                           std::string_view name,
                                           const DataType& type,
                                           SimContext& ctx) {
  const bool kUnpackedAggregate = (type.kind == DataTypeKind::kStruct ||
                                   type.kind == DataTypeKind::kUnion) &&
                                  !type.is_packed && !type.is_soft;
  if (!kUnpackedAggregate) return {};
  auto* key = ctx.GetArena().Create<std::string>(
      std::format("$param::{}::{}", scope, name));
  if (ctx.FindStructType(*key) == nullptr)
    RegisterTypeLayout(*key, &type, ctx, ctx.GetArena());
  return *key;
}

const StructTypeInfo* MethodClassTypedefLayout(std::string_view name,
                                               SimContext& ctx,
                                               std::string_view* key) {
  for (const ClassTypeInfo* c = ctx.CurrentMethodClass(); c != nullptr;
       c = c->parent) {
    if (c->decl == nullptr) continue;
    if (ClassAggregateTypedef(*c->decl, name) == nullptr) continue;
    if (!ClassHasValueParams(*c->decl)) return nullptr;
    std::string_view registered = ClassTypedefLayoutKey(*c, name, ctx);
    if (key != nullptr) *key = registered;
    return ctx.FindStructType(registered);
  }
  return nullptr;
}

}  // namespace delta
