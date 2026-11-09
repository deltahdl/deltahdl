#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

static const ClassMember* DeclaringMember(const ClassTypeInfo* type,
                                          std::string_view name) {
  for (const ClassTypeInfo* c = type; c != nullptr; c = c->parent) {
    if (c->decl == nullptr) continue;
    for (const ClassMember* m : c->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == name) return m;
    }
  }
  return nullptr;
}

static std::optional<PackedRange> DeclaredTypeRange(const DataType& dt,
                                                    uint32_t width,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (dt.packed_dim_left == nullptr || dt.packed_dim_right == nullptr ||
      !dt.extra_packed_dims.empty())
    return std::nullopt;
  PackedRange range{
      SelectBoundValue(EvalExpr(dt.packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(dt.packed_dim_right, ctx, arena))};
  if (range.HighIndex() - range.LowIndex() + 1 != width) return std::nullopt;
  return range;
}

std::optional<PackedRange> PropertyDeclaredRange(const ClassTypeInfo* type,
                                                 std::string_view field,
                                                 uint32_t width,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  const ClassMember* m = DeclaringMember(type, field);
  if (m == nullptr) return std::nullopt;
  return DeclaredTypeRange(m->data_type, width, ctx, arena);
}

namespace {

struct ClassNameDecl {
  const DataType* type = nullptr;
  size_t unpacked = 0;
};

}  // namespace

static ClassNameDecl HeaderParamDeclOf(const ClassDecl& decl,
                                       std::string_view name) {
  for (size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first != name) continue;
    auto dims = decl.param_port_unpacked_dims.find(name);
    return {&decl.param_types[i], dims == decl.param_port_unpacked_dims.end()
                                      ? 0
                                      : dims->second.size()};
  }
  return {};
}

static ClassNameDecl ClassNameDeclOf(const ClassTypeInfo* type,
                                     std::string_view name) {
  if (const ClassMember* m = DeclaringMember(type, name))
    return {&m->data_type, m->unpacked_dims.size()};
  return HeaderParamDeclOf(*type->decl, name);
}

const DataType* ClassNameType(const ClassTypeInfo* type,
                              std::string_view name) {
  return ClassNameDeclOf(type, name).type;
}

static std::vector<std::pair<Expr*, Expr*>> PackedDimsOf(const DataType& dt) {
  std::vector<std::pair<Expr*, Expr*>> dims;
  if (dt.packed_dim_left != nullptr)
    dims.emplace_back(dt.packed_dim_left, dt.packed_dim_right);
  dims.insert(dims.end(), dt.extra_packed_dims.begin(),
              dt.extra_packed_dims.end());
  return dims;
}

std::optional<PackedLevel> ClassNameLevel(const ClassTypeInfo* type,
                                          std::string_view name, size_t depth,
                                          uint32_t width, SimContext& ctx) {
  ClassNameDecl named = ClassNameDeclOf(type, name);
  if (named.type == nullptr || depth < named.unpacked) return std::nullopt;
  std::vector<std::pair<Expr*, Expr*>> dims = PackedDimsOf(*named.type);
  depth -= named.unpacked;
  if (depth >= dims.size()) return std::nullopt;
  Arena& arena = ctx.GetArena();
  PackedRange range{SelectBoundValue(EvalExpr(dims[depth].first, ctx, arena)),
                    SelectBoundValue(EvalExpr(dims[depth].second, ctx, arena))};
  auto span = static_cast<uint32_t>(range.HighIndex() - range.LowIndex() + 1);
  return PackedLevel{range, width / span};
}

std::optional<PackedRange> CalledFunctionRange(const Expr* base, uint32_t width,
                                               SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCall) return std::nullopt;
  const ModuleItem* func = ctx.FindFunction(base->callee);
  if (func == nullptr) return std::nullopt;
  return DeclaredTypeRange(func->return_type, width, ctx, arena);
}

PackedLevel EvaluatedPackedLevel(const Expr* left, const Expr* right,
                                 uint32_t width, SimContext& ctx,
                                 Arena& arena) {
  PackedRange range{SelectBoundValue(EvalExpr(left, ctx, arena)),
                    SelectBoundValue(EvalExpr(right, ctx, arena))};
  auto span = static_cast<uint32_t>(range.HighIndex() - range.LowIndex() + 1);
  return PackedLevel{range, width / span};
}

std::optional<PackedLevel> CastTypeLevel(const Expr* base, uint32_t width,
                                         SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCast) return std::nullopt;
  const Expr* ref = base->rhs;
  const DataType* type = ref != nullptr && ref->kind == ExprKind::kTypeRef
                             ? ref->type_value
                             : ctx.FindTypeDeclaration(CastTypeKey(base, ctx));
  if (type == nullptr || type->packed_dim_left == nullptr) return std::nullopt;
  return EvaluatedPackedLevel(type->packed_dim_left, type->packed_dim_right,
                              width, ctx, arena);
}

}  // namespace delta
