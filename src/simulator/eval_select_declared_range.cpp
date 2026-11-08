#include <cstdint>
#include <optional>
#include <string_view>

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

std::optional<PackedRange> CalledFunctionRange(const Expr* base, uint32_t width,
                                               SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCall) return std::nullopt;
  const ModuleItem* func = ctx.FindFunction(base->callee);
  if (func == nullptr) return std::nullopt;
  return DeclaredTypeRange(func->return_type, width, ctx, arena);
}

std::optional<PackedLevel> CastTypeLevel(const Expr* base, uint32_t width,
                                         SimContext& ctx, Arena& arena) {
  if (base->kind != ExprKind::kCast) return std::nullopt;
  const Expr* ref = base->rhs;
  const DataType* type = ref != nullptr && ref->kind == ExprKind::kTypeRef
                             ? ref->type_value
                             : ctx.FindTypeDeclaration(CastTypeKey(base, ctx));
  if (type == nullptr || type->packed_dim_left == nullptr) return std::nullopt;
  PackedRange range{
      SelectBoundValue(EvalExpr(type->packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(type->packed_dim_right, ctx, arena))};
  auto span = static_cast<uint32_t>(range.HighIndex() - range.LowIndex() + 1);
  return PackedLevel{range, width / span};
}

}  // namespace delta
