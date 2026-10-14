#include "elaborator/cross_bin_rules.h"

#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/cross_bin_with_covergroup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_eval.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// A cross whose bins are being checked: its covergroup's cross labels, what
// the covergroup reads, the bin in hand and where the reports go.
struct CrossSite {
  const CoverCrossDecl& cross;
  const std::unordered_set<std::string_view>& cross_labels;
  const CovergroupContext& ctx;
  std::string_view bin;
  DiagEngine& diag;
};

// The labels of the crosses `cg` declares.
std::unordered_set<std::string_view> CrossLabels(const CovergroupDecl& cg) {
  std::unordered_set<std::string_view> labels;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverCross &&
        !item.cover_cross->label.empty()) {
      labels.insert(item.cover_cross->label);
    }
  }
  return labels;
}

// §19.6.1.2: a constant `matches` count is a positive integer.
void CheckMatches(const SelectExpression& s, const CrossSite& site) {
  if (s.matches == nullptr) return;
  std::optional<int64_t> count = ConstEvalInt(s.matches);
  if (!count.has_value() || CrossMatchesCountIsLegal(*count)) return;
  site.diag.Error(s.matches->range.start,
                  std::format("the matches count of bin '{}' is {}; it is a "
                              "positive integer or $",
                              site.bin, *count),
                  Subclause("19.6.1.2"));
}

// The name a cross_identifier or a cross_set_expression written as a bare
// name selects through; empty for any other select expression.
std::string_view NameSelected(const SelectExpression& s) {
  if (s.kind == SelectExpressionKind::kCrossIdentifier) return s.cross_name;
  if (s.kind == SelectExpressionKind::kCrossSet && s.expr != nullptr &&
      s.expr->kind == ExprKind::kIdentifier) {
    return s.expr->text;
  }
  return {};
}

// §19.6.1.2: a cross_identifier names the enclosing cross alone; §19.6.1.4:
// an array a cross_set_expression names holds no integral, real or string
// elements, which no CrossValType structure is.
void CheckNameSelected(const SelectExpression& s, const CrossSite& site) {
  std::string_view name = NameSelected(s);
  if (name.empty() || name == site.cross.label) return;
  if (site.cross_labels.contains(name)) {
    if (!CrossIdentifierSelectIsLegal(name, site.cross.label)) {
      site.diag.Error(s.loc,
                      std::format("bin '{}' selects through cross '{}'; only "
                                  "the enclosing cross may be named there",
                                  site.bin, name),
                      Subclause("19.6.1.2"));
    }
    return;
  }
  std::optional<DataTypeKind> element = site.ctx.type_of(name);
  if (!site.ctx.arrays.kind_of(name).has_value() || !element.has_value() ||
      !(IsIntegralType(*element) || IsRealType(*element) ||
        *element == DataTypeKind::kString)) {
    return;
  }
  site.diag.Error(s.loc,
                  std::format("the cross_set_expression '{}' of bin '{}' is no "
                              "queue of the cross's CrossValType",
                              name, site.bin),
                  Subclause("19.6.1.4"));
}

void CheckSelect(const SelectExpression* s, const CrossSite& site) {
  if (s == nullptr) return;
  CheckMatches(*s, site);
  CheckNameSelected(*s, site);
  CheckSelect(s->lhs, site);
  CheckSelect(s->rhs, site);
}

}  // namespace

void CheckCrossBinRules(const CoverCrossDecl& cross, const CovergroupDecl& cg,
                        const CovergroupContext& ctx, DiagEngine& diag) {
  std::unordered_set<std::string_view> labels = CrossLabels(cg);
  for (const CrossBodyItem& body : cross.body) {
    if (body.kind != CrossBodyItemKind::kBinsSelection) continue;
    const CrossSite kSite{cross, labels, ctx, body.bins.name, diag};
    CheckSelect(body.bins.select, kSite);
  }
}

}  // namespace delta
