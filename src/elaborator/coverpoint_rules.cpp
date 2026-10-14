#include "elaborator/coverpoint_rules.h"

#include <cstdint>
#include <format>
#include <optional>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/value_kind.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Whether a value of kind `kind` is known to be neither integral nor real: a
// string, or a class handle, chandle, event or unpacked aggregate.
bool NeitherIntegralNorReal(ValueKind kind) {
  return kind == ValueKind::kString || kind == ValueKind::kOther;
}

// The kind of value `e` gives in a coverpoint of `cg`: a formal of `cg` by the
// type it is declared with, and any other expression as `ctx` answers.
ValueKind KindIn(const Expr* e, const CovergroupDecl& cg,
                 const CovergroupContext& ctx) {
  if (e->kind == ExprKind::kIdentifier) {
    if (const FunctionArg* formal = FindCovergroupFormal(cg, e->text)) {
      return KindOfDeclaredType(formal->data_type, ctx.is_class);
    }
  }
  return ctx.value_kind(e);
}

// §19.5: a data type written for a coverpoint is an integral type or real.
void CheckDataType(const CoverPointDecl& cp, const CovergroupContext& ctx,
                   DiagEngine& diag) {
  if (!cp.has_data_type ||
      !NeitherIntegralNorReal(KindOfDeclaredType(cp.data_type, ctx.is_class))) {
    return;
  }
  diag.Error(cp.loc,
             std::format("coverpoint '{}' is declared with a data type that is "
                         "neither integral nor real",
                         cp.label),
             Subclause("19.5"));
}

// §19.5: a coverpoint covers an integral or real expression.
void CheckExpression(const CoverPointDecl& cp, const CovergroupDecl& cg,
                     const CovergroupContext& ctx, DiagEngine& diag) {
  if (!NeitherIntegralNorReal(KindIn(cp.expr, cg, ctx))) return;
  diag.Error(cp.expr->range.start,
             "a coverpoint covers an integral or real expression, and this "
             "expression is neither",
             Subclause("19.5"));
}

// §19.5 with §19.5.5: a default bin cannot be explicitly ignored.
void CheckIgnoredDefault(const BinsOrOptions& bins, DiagEngine& diag) {
  if (bins.keyword != BinsKeyword::kIgnoreBins ||
      (bins.kind != BinsOrOptionsKind::kDefault &&
       bins.kind != BinsOrOptionsKind::kDefaultSequence)) {
    return;
  }
  diag.Error(
      bins.loc,
      std::format("ignore_bins '{}' cannot ignore the default bin", bins.name),
      Subclause("19.5"));
}

// §19.5.1: a fixed number of bins is given by a positive integral expression.
void CheckBinCount(const BinsOrOptions& bins, DiagEngine& diag) {
  if (bins.array_size == nullptr) return;
  std::optional<int64_t> count = ConstEvalInt(bins.array_size);
  if (!count.has_value() || *count > 0) return;
  diag.Error(bins.array_size->range.start,
             std::format("bins '{}' asks for {} bins; the number of bins is a "
                         "positive integral value",
                         bins.name, *count),
             Subclause("19.5.1"));
}

// §19.5.1.1: the coverpoint a bin names before `with` is the one holding the
// bin, and the `with` expression gives a value assignment compatible with an
// integral type.
void CheckWith(const BinsOrOptions& bins, const CoverPointDecl& cp,
               const CovergroupDecl& cg, const CovergroupContext& ctx,
               DiagEngine& diag) {
  if (bins.kind == BinsOrOptionsKind::kCoverPointWith &&
      bins.with_cover_point != CoverpointName(cp)) {
    diag.Error(bins.loc,
               std::format("bin '{}' names coverpoint '{}' before 'with'; only "
                           "the coverpoint holding the bin may stand there",
                           bins.name, bins.with_cover_point),
               Subclause("19.5.1.1"));
  }
  if (bins.with_expr != nullptr &&
      NeitherIntegralNorReal(KindIn(bins.with_expr, cg, ctx))) {
    diag.Error(bins.with_expr->range.start,
               std::format("the 'with' expression of bin '{}' is not "
                           "assignment compatible with an integral type",
                           bins.name),
               Subclause("19.5.1.1"));
  }
}

}  // namespace

void CheckCoverpointRules(const CoverPointDecl& cp, const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag) {
  CheckDataType(cp, ctx, diag);
  CheckExpression(cp, cg, ctx, diag);
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    CheckIgnoredDefault(bins, diag);
    CheckBinCount(bins, diag);
    CheckWith(bins, cp, cg, ctx, diag);
  }
}

}  // namespace delta
