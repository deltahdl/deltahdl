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

static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  if (aa->has_default) return aa->default_value;
  return aa->is_4state ? MakeAllX(arena, aa->elem_width)
                       : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

// `loc` is where the index was written, which the report names: the array
// object carries no position and the name is a string.
static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx, SourceLoc loc) {
  if (!aa->has_default)
    ctx.GetDiag().Warning(loc,
                          "associative array '" + std::string(name) +
                              "': read of non-existent index",
                          Subclause("7.8.6"));
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = AssocStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
  return AssocDefault(aa, arena);
}

static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto val = EvalExpr(idx_expr, ctx, arena);
  if (HasUnknownBits(val)) {
    // §7.8.6: an x/z index is an invalid read. A configured user default
    // suppresses the diagnostic and supplies the returned value (see §7.9.11),
    // matching the nonexistent-entry path in WarnAssocMiss.
    if (!aa->has_default)
      ctx.GetDiag().Warning(
          idx_expr->range.start,
          "associative array '" + std::string(name) + "': index contains x/z",
          Subclause("7.8.6"));
    return AssocDefault(aa, arena);
  }
  auto key =
      AssocIntKey(val, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx, idx_expr->range.start);
  return AssocDefault(aa, arena);
}

// §7.8: the array an element select reads is a declared one under its bare
// name or, §8.5 restricting no property's type, a property of an object -- the
// running method's own by its bare name (§8.11) or any object's through a
// handle, `o.count[k]` -- which FindAssocArrayOfBase resolves. Only the bare
// name of a declared array was read here before, so `m_severity_count[s]` in a
// method of UVM's uvm_report_server fell to a bit-select of the property's
// scalar carrier and read 0 whatever the entry held. The name a §7.8.6 report
// gives is the property's own for a property.
//
// §7.8 with §7.4: the array may be an element of an associative array whose
// elements are associative arrays, `m["a"][2]`, and the report then names the
// array it is an element of.
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
  out = aa->is_string_key ? AssocReadStr(aa, expr->index, name, ctx, arena)
                          : AssocReadInt(aa, expr->index, name, ctx, arena);
  TakeElementSignedness(*aa, out);
  return true;
}

}  // namespace delta
