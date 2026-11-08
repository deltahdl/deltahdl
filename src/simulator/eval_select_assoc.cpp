#include "simulator/eval_select_assoc.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

void TakeElementSignedness(const AssocArrayObject& aa, Logic4Vec& val) {
  if (val.is_string || val.is_real || !aa.elem_class.empty()) return;
  val.is_signed = aa.is_signed;
}

static Logic4Vec AssocDefault(const AssocArrayObject* aa, const Expr* select,
                              SimContext& ctx, Arena& arena) {
  if (aa->has_default) return aa->default_value;
  return NonexistentElementOf(select, aa->is_4state, aa->elem_width, ctx,
                              arena);
}

static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx, SourceLoc loc) {
  if (!aa->has_default)
    ctx.GetDiag().Warning(loc,
                          "associative array '" + std::string(name) +
                              "': read of non-existent index",
                          Subclause("7.8.6"));
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* select,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  const Expr* idx_expr = select->index;
  auto s = AssocStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
  return AssocDefault(aa, select, ctx, arena);
}

static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* select,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  const Expr* idx_expr = select->index;
  auto val = EvalExpr(idx_expr, ctx, arena);
  if (HasUnknownBits(val)) {
    if (!aa->has_default)
      ctx.GetDiag().Warning(
          idx_expr->range.start,
          "associative array '" + std::string(name) + "': index contains x/z",
          Subclause("7.8.6"));
    return AssocDefault(aa, select, ctx, arena);
  }
  auto key =
      AssocIntKey(val, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
  return AssocDefault(aa, select, ctx, arena);
}

static std::string_view AssocReportName(const Expr* base) {
  while (base->kind == ExprKind::kSelect && base->base != nullptr)
    base = base->base;
  if (base->kind == ExprKind::kIdentifier) return base->text;
  return base->rhs != nullptr ? base->rhs->text : std::string_view{};
}

bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                    Logic4Vec& out) {
  if (!expr->base || expr->index_end) return false;
  auto* aa = FindAssocArrayOfBase(expr->base, ctx, arena);
  if (!aa) return false;
  std::string_view name = AssocReportName(expr->base);
  out = aa->is_string_key ? AssocReadStr(aa, expr, name, ctx, arena)
                          : AssocReadInt(aa, expr, name, ctx, arena);
  TakeElementSignedness(*aa, out);
  return true;
}

}  // namespace delta
