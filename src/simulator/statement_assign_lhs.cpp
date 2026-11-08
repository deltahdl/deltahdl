#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kSelect && expr->base != nullptr &&
      expr->index != nullptr && expr->index_end == nullptr &&
      expr->index->kind == ExprKind::kIntegerLiteral) {
    BuildLhsName(expr->base, out);
    out += "[" + std::to_string(expr->index->int_val) + "]";
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->index_end) return nullptr;
  std::string_view key = ArrayRootKey(lhs->base, ctx.GetArena());
  if (key.empty()) return nullptr;
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  if (HasUnknownBits(idx)) return nullptr;
  auto elem_name =
      std::string(key) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return false;
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

std::string_view CompoundRootName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return (e != nullptr && e->kind == ExprKind::kIdentifier)
             ? e->text
             : std::string_view{};
}

static bool OutermostIndexIsOutOfRange(const Expr* lhs, const ArrayInfo& info,
                                       SimContext& ctx, Arena& arena) {
  const Expr* outer = lhs;
  while (outer->base != nullptr && outer->base->kind == ExprKind::kSelect)
    outer = outer->base;
  if (outer->index == nullptr) return false;
  auto idx = EvalExpr(outer->index, ctx, arena);
  if (HasUnknownBits(idx)) return true;
  auto value = idx.ToUint64();
  return value < info.lo || value >= static_cast<uint64_t>(info.lo) + info.size;
}

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena, bool* absent_element) {
  if (absent_element != nullptr) *absent_element = false;
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  if (auto* var = ctx.FindVariable(compound)) return var;
  const ArrayInfo* info = ctx.FindArrayInfo(CompoundRootName(lhs));
  if (info != nullptr && OutermostIndexIsOutOfRange(lhs, *info, ctx, arena)) {
    if (absent_element != nullptr) *absent_element = true;
    return nullptr;
  }
  uint32_t width = info != nullptr ? info->elem_width : 32;
  auto& name = *arena.Create<std::string>(std::move(compound));
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) {
    return ctx.FindVariable(IdentifierLookupKey(lhs));
  }
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    std::string rooted = RootedReferenceKey(name);
    if (!rooted.empty()) {
      if (Variable* var = ctx.FindVariable(rooted)) return var;
    }
    auto resolved = StripRootPrefix(name);
    if (Variable* var = ctx.FindVariable(resolved)) return var;
    return FunctionStaticLocal(lhs, ctx, ctx.GetArena());
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

}  // namespace delta
