#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/virtual_interface.h"

namespace delta {

static std::string_view InlineFormalLayoutKey(const FunctionArg& param,
                                              SimContext& ctx) {
  const DataType& dt = param.data_type;
  if (dt.struct_members.empty()) return {};
  std::string key =
      std::format("{}@{:x}", param.name, reinterpret_cast<uintptr_t>(&dt));
  if (const StructTypeInfo* info = ctx.FindStructType(key)) {
    return info->type_name;
  }
  Arena& arena = ctx.GetArena();
  auto* owned = arena.Create<std::string>(std::move(key));
  RegisterAggregateLayout(*owned, &dt, DeclaredTypeWidth(dt, ctx), ctx, arena);
  return *owned;
}

std::string_view FormalLayoutKey(const FunctionArg& param, SimContext& ctx) {
  const DataType& dt = param.data_type;
  if (!dt.type_name.empty() && ctx.FindStructType(dt.type_name) != nullptr)
    return dt.type_name;
  return InlineFormalLayoutKey(param, ctx);
}

static bool TryEvalTaggedPatternActual(const FunctionArg& param,
                                       const Expr* actual, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr ||
      actual->lhs == nullptr)
    return false;
  const Expr* pattern = UnwrapTypedPattern(actual->lhs);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  const StructTypeInfo* member =
      TaggedMemberLayout(*ctx.FindStructType(key), actual->rhs->text);
  if (member == nullptr) return false;
  out = EvalStructPatternValue(pattern, member, ctx, arena);
  return true;
}

bool TryEvalPatternActual(const FunctionArg& param, const Expr* actual,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalTaggedPatternActual(param, actual, ctx, arena, out)) return true;
  const Expr* pattern = UnwrapTypedPattern(actual);
  if (pattern->kind != ExprKind::kAssignmentPattern) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  const StructTypeInfo* layout = ctx.FindStructType(key);
  if (layout->is_union) return false;
  out = EvalStructPatternValue(pattern, layout, ctx, arena);
  return true;
}

bool TryBindTaggedActual(const FunctionArg& param, const Expr* actual,
                         SimContext& ctx) {
  if (actual->kind != ExprKind::kTagged || actual->rhs == nullptr) return false;
  std::string_view key = FormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  ctx.SetVariableStructType(param.name, key);
  ctx.SetVariableTag(param.name, actual->rhs->text);
  return true;
}

bool TryBindInlineAggregateFormal(const FunctionArg& param, SimContext& ctx) {
  std::string_view key = InlineFormalLayoutKey(param, ctx);
  if (key.empty()) return false;
  ctx.SetVariableStructType(param.name, key);
  return true;
}

bool TryBindNamedAggregateFormal(const FunctionArg& param, SimContext& ctx) {
  std::string_view type_name = param.data_type.type_name;
  if (type_name.empty() || ctx.FindStructType(type_name) == nullptr)
    return false;
  ctx.SetVariableStructType(param.name, type_name);
  return true;
}

uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx, Arena& arena) {
  if (!dt.packed_dim_left || !dt.packed_dim_right) {
    if (!DeclaredClassKey(dt, ctx, arena).empty()) return 64;
    if (DeclaresAVirtualInterface(dt, ctx)) return 64;
    return DeclaredTypeWidth(dt, ctx);
  }
  auto span = [&](const Expr* l, const Expr* r) -> uint32_t {
    int64_t lv = static_cast<int64_t>(EvalExpr(l, ctx, arena).ToUint64());
    int64_t rv = static_cast<int64_t>(EvalExpr(r, ctx, arena).ToUint64());
    return static_cast<uint32_t>((lv >= rv ? lv - rv : rv - lv) + 1);
  };
  uint32_t width = span(dt.packed_dim_left, dt.packed_dim_right);
  for (const auto& [l, r] : dt.extra_packed_dims) width *= span(l, r);
  return width;
}

}  // namespace delta
