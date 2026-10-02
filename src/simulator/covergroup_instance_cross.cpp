#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <set>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"

namespace delta {

namespace {

// A cross product, as a tuple of indices into the bins of the crossed
// coverpoints, in the order the cross lists them (§19.6).
using Tuple = std::vector<size_t>;

// What a select_expression of a cross reads (§19.6.1): the instance, the
// index into its points of each coverpoint the cross crosses, and the values
// of each `intersect` the expression holds, read once.
struct CrossSelector {
  const CovergroupInstance& inst;
  std::vector<size_t> points;
  std::unordered_map<const SelectExpression*, std::vector<CoverValueRange>>
      intersects;
};

// §19.6: the coverpoint `name` of the instance, by index into its points; a
// variable the cross names that no coverpoint does is given an implicit
// coverpoint, as though `coverpoint name;` had been written.
size_t CrossedPoint(CovergroupInstance& inst, std::string_view name,
                    size_t index, SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < inst.points.size(); ++i) {
    if (inst.points[i].point->name == name) return i;
  }
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  auto* decl = arena.Create<CoverPointDecl>();
  decl->expr = id;
  BuildCoverpoint(inst, *decl, index, ctx, arena);
  return inst.points.size() - 1;
}

// Reads the values of every `intersect` in a select_expression, a `$` bound
// standing for the end of the values of the coverpoint it names.
void ReadIntersects(const SelectExpression* select, CrossSelector& selector,
                    SimContext& ctx, Arena& arena) {
  if (select == nullptr) return;
  if (select->kind == SelectExpressionKind::kBinsOf &&
      !select->intersect.empty()) {
    for (size_t point : selector.points) {
      const SampledCoverpoint& sampled = selector.inst.points[point];
      if (sampled.point->name == select->bins_of) {
        selector.intersects[select] =
            CovergroupRangeValues(select->intersect, sampled, ctx, arena);
      }
    }
  }
  ReadIntersects(select->lhs, selector, ctx, arena);
  ReadIntersects(select->rhs, selector, ctx, arena);
}

bool InValues(int64_t v, const std::vector<CoverValueRange>& values) {
  return std::ranges::any_of(
      values, [&](const CoverValueRange& r) { return r.lo <= v && v <= r.hi; });
}

// §19.6.1: whether a coverpoint bin's values intersect `values`; a transition
// bin's values are the last of each of its transitions.
bool BinIntersects(const CoverBin& bin,
                   const std::vector<CoverValueRange>& values) {
  for (int64_t v : CoverageDB::BinsofBinValues(bin)) {
    if (InValues(v, values)) return true;
  }
  return std::ranges::any_of(bin.ranges, [&](const CoverValueRange& r) {
    return std::ranges::any_of(values, [&](const CoverValueRange& v) {
      return v.lo <= r.hi && r.lo <= v.hi;
    });
  });
}

// §19.6.1: whether the bin `bin` of a coverpoint is the one, or one of the
// array of bins, that `binsof ( cover_point . bin )` names.
bool BinNamed(const CoverBin& bin, std::string_view name) {
  return bin.name == name ||
         (bin.name.starts_with(name) && bin.name.size() > name.size() &&
          bin.name[name.size()] == '[');
}

bool SelectsBinsOf(const SelectExpression& select, const Tuple& tuple,
                   const CrossSelector& selector) {
  for (size_t i = 0; i < selector.points.size(); ++i) {
    const CoverPoint& cp = *selector.inst.points[selector.points[i]].point;
    if (cp.name != select.bins_of) continue;
    const CoverBin& bin = cp.bins[tuple[i]];
    if (!select.bins_of_bin.empty() && !BinNamed(bin, select.bins_of_bin)) {
      return false;
    }
    auto it = selector.intersects.find(&select);
    return it == selector.intersects.end() || BinIntersects(bin, it->second);
  }
  return false;
}

// §19.6.1: whether a select_expression selects the cross product `tuple`.
bool Selects(const SelectExpression& select, const Tuple& tuple,
             const CrossSelector& selector) {
  switch (select.kind) {
    case SelectExpressionKind::kBinsOf:
      return SelectsBinsOf(select, tuple, selector);
    case SelectExpressionKind::kNot:
      return !Selects(*select.lhs, tuple, selector);
    case SelectExpressionKind::kAnd:
      return Selects(*select.lhs, tuple, selector) &&
             Selects(*select.rhs, tuple, selector);
    case SelectExpressionKind::kOr:
      return Selects(*select.lhs, tuple, selector) ||
             Selects(*select.rhs, tuple, selector);
    case SelectExpressionKind::kParenthesized:
      return Selects(*select.lhs, tuple, selector);
    case SelectExpressionKind::kCrossIdentifier:
      return true;
    default:
      return false;
  }
}

// A cross's bins_selection items read as the products each selects: the
// `bins` (§19.6.1), and the products ignore_bins (§19.6.2) and illegal_bins
// (§19.6.3) take out of every bin of the cross.
struct CrossSelections {
  std::vector<CrossBin> user_bins;
  std::vector<const Expr*> user_guards;
  std::set<Tuple> in_user_bins;
  std::set<Tuple> excluded;
};

CrossSelections ReadSelections(const CoverCrossDecl& decl,
                               const std::vector<Tuple>& products,
                               const CrossSelector& selector,
                               SampledCross& sampled) {
  CrossSelections selections;
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind != CrossBodyItemKind::kBinsSelection) continue;
    std::vector<Tuple> selected;
    for (const Tuple& tuple : products) {
      if (Selects(*item.bins.select, tuple, selector))
        selected.push_back(tuple);
    }
    if (item.bins.keyword == BinsKeyword::kBins) {
      selections.in_user_bins.insert(selected.begin(), selected.end());
      CrossBin bin;
      bin.name = std::string(item.bins.name);
      bin.bin_tuples = std::move(selected);
      selections.user_bins.push_back(std::move(bin));
      selections.user_guards.push_back(item.bins.iff);
      continue;
    }
    selections.excluded.insert(selected.begin(), selected.end());
    if (item.bins.keyword == BinsKeyword::kIllegalBins) {
      sampled.illegal.push_back({std::string(item.bins.name), selected});
    }
  }
  return selections;
}

// The cross's bins: each user-defined bin with the products ignore_bins and
// illegal_bins take out removed, a bin left with none taking no part
// (§19.11.2); then an automatic bin for every other product that no
// user-defined bin selects, or none at all where cross_retain_auto_bins is
// false and the cross defines a bin of its own (§19.6.1, Table 19-1).
void AddCrossBins(const CovergroupInstance& inst, CrossCover& cross,
                  const std::vector<Tuple>& products,
                  CrossSelections& selections, SampledCross& sampled) {
  for (size_t i = 0; i < selections.user_bins.size(); ++i) {
    CrossBin& bin = selections.user_bins[i];
    std::erase_if(bin.bin_tuples, [&](const Tuple& t) {
      return selections.excluded.contains(t);
    });
    if (bin.bin_tuples.empty()) continue;
    if (selections.user_guards[i] != nullptr) {
      sampled.bin_guards.emplace_back(cross.bins.size(),
                                      selections.user_guards[i]);
    }
    cross.bins.push_back(std::move(bin));
  }
  bool retain =
      cross.option.cross_retain_auto_bins || selections.user_bins.empty();
  for (const Tuple& tuple : products) {
    if (!retain || selections.in_user_bins.contains(tuple) ||
        selections.excluded.contains(tuple)) {
      continue;
    }
    CrossBin bin;
    bin.name = CoverageDB::CrossProductName(inst.group, &cross, tuple);
    bin.bin_tuples.push_back(tuple);
    cross.bins.push_back(std::move(bin));
  }
  for (CrossBin& bin : cross.bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, cross.option.at_least));
  }
}

}  // namespace

void BuildCross(CovergroupInstance& inst, const CoverCrossDecl& decl,
                size_t index, SimContext& ctx, Arena& arena) {
  CrossCover cross;
  cross.name = decl.label.empty() ? std::format("__cross_{}", index)
                                  : std::string(decl.label);
  cross.option.at_least = inst.group->options.at_least;
  cross.option.cross_num_print_missing =
      inst.group->options.cross_num_print_missing;
  cross.option.cross_retain_auto_bins =
      inst.group->options.cross_retain_auto_bins;
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind == CrossBodyItemKind::kOption) {
      ApplyCrossOption(cross, item.option, ctx, arena);
    }
  }
  std::vector<size_t> points;
  for (const CrossItem& item : decl.items) {
    points.push_back(CrossedPoint(inst, item.name, index, ctx, arena));
    cross.coverpoint_names.push_back(inst.points[points.back()].point->name);
  }
  SampledCross sampled;
  sampled.index = inst.group->crosses.size();
  sampled.iff = decl.iff;
  CrossCover* added = CoverageDB::AddCross(inst.group, std::move(cross));
  CrossSelector selector{inst, std::move(points), {}};
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind == CrossBodyItemKind::kBinsSelection) {
      ReadIntersects(item.bins.select, selector, ctx, arena);
    }
  }
  std::vector<Tuple> products =
      CoverageDB::CrossProductTuples(inst.group, added);
  CrossSelections selections =
      ReadSelections(decl, products, selector, sampled);
  AddCrossBins(inst, *added, products, selections, sampled);
  inst.crosses.push_back(std::move(sampled));
}

}  // namespace delta
