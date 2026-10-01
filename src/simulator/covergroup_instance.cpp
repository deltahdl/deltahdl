#include "simulator/covergroup_instance.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// CoverBin lists every value a bin holds, so a range is expanded value by
// value; this bounds how many values one range contributes.
constexpr int64_t kMaxRangeValues = int64_t{1} << 16;

struct ValueBounds {
  int64_t min = 0;
  int64_t max = 0;
};

// The values an expression of `v`'s width and signedness can take, which the
// `$` bound of a range (§19.5.1) and the automatic bins of a coverpoint
// (§19.5.3) span.
ValueBounds BoundsOf(const Logic4Vec& v) {
  uint32_t width = std::min<uint32_t>(v.width, 63);
  int64_t span = int64_t{1} << (v.is_signed ? width - 1 : width);
  int64_t min = v.is_signed ? -span : 0;
  return {min, min + (v.is_signed ? 2 * span : span) - 1};
}

// Reads the expressions a covergroup's declaration writes: a name of one of
// its formals is the actual new() gave it (§19.3), and anything else is read
// in the scope the instance stands in.
class CovergroupReader {
 public:
  CovergroupReader(const CovergroupInstance& inst, SimContext& ctx,
                   Arena& arena)
      : inst_(inst), ctx_(ctx), arena_(arena) {}

  int64_t Value(const Expr* e) const {
    if (e->kind == ExprKind::kIdentifier) {
      auto it = inst_.formals.find(e->text);
      if (it != inst_.formals.end()) return it->second;
    }
    return SelectBoundValue(EvalExpr(e, ctx_, arena_));
  }

  Logic4Vec Eval(const Expr* e) const { return EvalExpr(e, ctx_, arena_); }

  // §19.5.1: the values of a covergroup_range_list, in the order written,
  // duplicates retained; a `$` bound stands for the end of `bounds`.
  std::vector<int64_t> Values(const std::vector<CovergroupValueRange>& ranges,
                              ValueBounds bounds) const {
    std::vector<int64_t> values;
    for (const CovergroupValueRange& range : ranges) {
      if (range.kind == CovergroupValueRangeKind::kValue) {
        values.push_back(Value(range.lo));
      } else if (range.kind == CovergroupValueRangeKind::kRange) {
        int64_t lo = range.lo != nullptr ? Value(range.lo) : bounds.min;
        int64_t hi = range.hi != nullptr ? Value(range.hi) : bounds.max;
        hi = std::min(hi, lo + kMaxRangeValues - 1);
        for (int64_t v = lo; v <= hi; ++v) values.push_back(v);
      }
    }
    return values;
  }

 private:
  const CovergroupInstance& inst_;
  SimContext& ctx_;
  Arena& arena_;
};

CoverBinKind BinKindOf(BinsKeyword keyword) {
  if (keyword == BinsKeyword::kIllegalBins) return CoverBinKind::kIllegal;
  if (keyword == BinsKeyword::kIgnoreBins) return CoverBinKind::kIgnore;
  return CoverBinKind::kExplicit;
}

// §19.5.1: one bin for all the values, one per value for `[]`, or the values
// spread over the N bins of `[N]`, B = values / N to each and the rest to the
// last, with a bin past the values left empty.
void AddValueBins(CoverPoint* cp, const BinsOrOptions& bins,
                  const std::vector<int64_t>& values,
                  const CovergroupReader& reader) {
  CoverBin bin;
  bin.kind = BinKindOf(bins.keyword);
  if (!bins.is_array) {
    bin.name = std::string(bins.name);
    bin.values = values;
    CoverageDB::AddBin(cp, bin);
    return;
  }
  if (bins.array_size == nullptr) {
    for (int64_t v : values) {
      bin.name = CoverageDB::StateBinName(bins.name, v);
      bin.values = {v};
      CoverageDB::AddBin(cp, bin);
    }
    return;
  }
  auto count =
      static_cast<size_t>(std::max<int64_t>(1, reader.Value(bins.array_size)));
  size_t per_bin = std::max<size_t>(1, values.size() / count);
  for (size_t i = 0; i < count; ++i) {
    size_t begin = std::min(values.size(), i * per_bin);
    size_t end = i + 1 == count ? values.size()
                                : std::min(values.size(), begin + per_bin);
    bin.name = CoverageDB::StateBinName(bins.name, static_cast<int64_t>(i));
    bin.values.assign(values.begin() + static_cast<std::ptrdiff_t>(begin),
                      values.begin() + static_cast<std::ptrdiff_t>(end));
    CoverageDB::AddBin(cp, bin);
  }
}

// §19.5.5 and §19.5.6: a value an ignore_bins or illegal_bins holds is
// excluded from coverage, so it is taken out of the coverpoint's other bins,
// and a bin it leaves holding nothing takes no part in coverage.
void ExcludeIgnoredAndIllegalValues(CoverPoint* cp) {
  std::unordered_set<int64_t> excluded;
  for (const CoverBin& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIgnore ||
        bin.kind == CoverBinKind::kIllegal) {
      excluded.insert(bin.values.begin(), bin.values.end());
    }
  }
  for (CoverBin& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kExplicit) continue;
    std::erase_if(bin.values,
                  [&](int64_t v) { return excluded.count(v) != 0; });
  }
}

// §19.5: the name a coverpoint goes by, its label or, unlabelled, the variable
// its expression names; any other is given its position.
std::string CoverpointName(const CoverPointDecl& cp, size_t index) {
  if (!cp.label.empty()) return std::string(cp.label);
  if (cp.expr->kind == ExprKind::kIdentifier) return std::string(cp.expr->text);
  return std::format("__coverpoint_{}", index);
}

void BuildCoverpoint(CovergroupInstance& inst, const CoverPointDecl& decl,
                     size_t index, const CovergroupReader& reader) {
  std::string name = CoverpointName(decl, index);
  CoverPoint* cp = CoverageDB::AddCoverPoint(inst.group, name);
  ValueBounds bounds = BoundsOf(reader.Eval(decl.expr));
  for (const BinsOrOptions& bins : decl.bins) {
    if (bins.kind == BinsOrOptionsKind::kValues) {
      AddValueBins(cp, bins, reader.Values(bins.ranges, bounds), reader);
    } else if (bins.kind == BinsOrOptionsKind::kDefault) {
      CoverBin bin;
      bin.name = std::string(bins.name);
      bin.kind = CoverBinKind::kDefault;
      CoverageDB::AddBin(cp, bin);
    }
  }
  ExcludeIgnoredAndIllegalValues(cp);
  CoverageDB::AutoCreateBins(cp, bounds.min, bounds.max);
  inst.points.emplace_back(std::move(name), decl.expr);
}

// §19.6: a cross of the named coverpoints, with the automatic cross bins of
// their bins' products, and the illegal_bins selections §19.6.3 reports.
void BuildCross(CovergroupInstance& inst, const CoverCrossDecl& decl,
                size_t index, const CovergroupReader& reader) {
  CrossCover cross;
  cross.name = decl.label.empty() ? std::format("__cross_{}", index)
                                  : std::string(decl.label);
  cross.coverpoint_names.reserve(decl.items.size());
  for (const CrossItem& item : decl.items) {
    cross.coverpoint_names.emplace_back(item.name);
  }
  CoverageDB::EnsureCrossCoverPoints(inst.group, cross.coverpoint_names);
  CrossCover* added = CoverageDB::AddCross(inst.group, std::move(cross));
  CoverageDB::AutoCreateCrossBins(inst.group, added);
  for (const CrossBodyItem& item : decl.body) {
    const SelectExpression* select = item.bins.select;
    if (item.kind == CrossBodyItemKind::kBinsSelection &&
        item.bins.keyword == BinsKeyword::kIllegalBins &&
        select->kind == SelectExpressionKind::kBinsOf &&
        !select->intersect.empty()) {
      inst.illegal_selections.push_back(
          {added->name, std::string(item.bins.name),
           std::string(select->bins_of),
           reader.Values(select->intersect, ValueBounds{})});
    }
  }
}

// §19.8: samples the instance, reporting a value an illegal_bins holds
// (§19.5.6) and a tuple an illegal_bins selection of a cross covers (§19.6.3)
// as run-time errors at the call that sampled it.
void SampleInstance(CovergroupInstance& inst, SourceLoc loc, SimContext& ctx,
                    Arena& arena) {
  CovergroupReader reader(inst, ctx, arena);
  std::vector<std::pair<std::string, int64_t>> values;
  values.reserve(inst.points.size());
  for (const auto& [name, expr] : inst.points) {
    values.emplace_back(name, reader.Value(expr));
  }
  std::vector<uint64_t> violations;
  violations.reserve(inst.group->coverpoints.size());
  for (const CoverPoint& cp : inst.group->coverpoints) {
    violations.push_back(cp.illegal_violations);
  }
  ctx.CoverageData().Sample(inst.group, values);
  // A coverpoint's illegal_violations rises only on a value Sample() found
  // under its name, so the lookup below finds one.
  constexpr auto kPointName = &std::pair<std::string, int64_t>::first;
  size_t index = 0;
  for (const CoverPoint& cp : inst.group->coverpoints) {
    if (cp.illegal_violations > violations[index++]) {
      ctx.GetDiag().Error(
          loc,
          std::format("sampled value {} of coverpoint '{}' falls in an "
                      "illegal bin",
                      std::ranges::find(values, cp.name, kPointName)->second,
                      cp.name),
          Subclause("19.5.6"));
    }
  }
  for (const IllegalCrossSelection& sel : inst.illegal_selections) {
    bool hit = std::ranges::any_of(values, [&](const auto& sampled) {
      return sampled.first == sel.cover_point &&
             std::ranges::find(sel.values, sampled.second) != sel.values.end();
    });
    if (hit) {
      ctx.GetDiag().Error(
          loc,
          std::format("sampled values of cross '{}' fall in its illegal bins "
                      "'{}'",
                      sel.cross_name, sel.bins_name),
          Subclause("19.6.3"));
    }
  }
}

// §19.8: the optional ref-int pair of get_coverage() and get_inst_coverage()
// receives the covered and the defined bins.
void WriteCount(const Expr* arg, int32_t count, SimContext& ctx, Arena& arena) {
  Variable* v = ctx.FindVariable(arg->text);
  if (v != nullptr) {
    v->value =
        MakeLogic4VecVal(arena, v->value.width, static_cast<uint64_t>(count));
  }
}

Logic4Vec ReportCoverage(CovergroupInstance& inst, const Expr* call,
                         bool instance, SimContext& ctx, Arena& arena) {
  int32_t covered = 0;
  int32_t total = 0;
  double coverage =
      instance ? CoverageDB::GetInstCoverage(inst.group, covered, total)
               : CoverageDB::GetCoverage(inst.group, covered, total);
  if (call->args.size() == 2) {
    WriteCount(call->args[0], covered, ctx, arena);
    WriteCount(call->args[1], total, ctx, arena);
  }
  return MakeRealVec(arena, coverage, 64);
}

using CovergroupMethod = Logic4Vec (*)(CovergroupInstance&, const Expr*,
                                       SimContext&, Arena&);

constexpr std::array<std::pair<std::string_view, CovergroupMethod>, 5>
    kCovergroupMethods = {{
        {"sample",
         [](CovergroupInstance& inst, const Expr* call, SimContext& ctx,
            Arena& arena) {
           SampleInstance(inst, call->range.start, ctx, arena);
           return MakeLogic4VecVal(arena, 1, 0);
         }},
        {"get_coverage",
         [](CovergroupInstance& inst, const Expr* call, SimContext& ctx,
            Arena& arena) {
           return ReportCoverage(inst, call, false, ctx, arena);
         }},
        {"get_inst_coverage",
         [](CovergroupInstance& inst, const Expr* call, SimContext& ctx,
            Arena& arena) {
           return ReportCoverage(inst, call, true, ctx, arena);
         }},
        {"start",
         [](CovergroupInstance& inst, const Expr*, SimContext&, Arena& arena) {
           CoverageDB::Start(inst.group);
           return MakeLogic4VecVal(arena, 1, 0);
         }},
        {"stop",
         [](CovergroupInstance& inst, const Expr*, SimContext&, Arena& arena) {
           CoverageDB::Stop(inst.group);
           return MakeLogic4VecVal(arena, 1, 0);
         }},
    }};

}  // namespace

CovergroupInstance* CovergroupTable::Create(std::string_view key) {
  return &instances_[std::string(key)];
}

CovergroupInstance* CovergroupTable::Find(std::string_view name,
                                          const SimContext& ctx) {
  for (const std::string& key : ctx.ScopedObjectKeys(name)) {
    auto it = instances_.find(key);
    if (it != instances_.end()) return &it->second;
  }
  return nullptr;
}

void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            SimContext& ctx, Arena& arena) {
  CovergroupInstance* inst = ctx.Covergroups().Create(name);
  inst->decl = var.covergroup;
  inst->group = ctx.CoverageData().CreateGroup(std::string(name));
  CovergroupReader reader(*inst, ctx, arena);
  const std::vector<FunctionArg>& formals = var.covergroup->formals;
  size_t bound = std::min(formals.size(), var.init_expr->args.size());
  for (size_t i = 0; i < bound; ++i) {
    inst->formals[formals[i].name] = reader.Value(var.init_expr->args[i]);
  }
  size_t index = 0;
  for (const CoverageSpecOrOption& item : var.covergroup->items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      BuildCoverpoint(*inst, *item.cover_point, index, reader);
    } else if (item.kind == CoverageSpecKind::kCoverCross) {
      BuildCross(*inst, *item.cover_cross, index, reader);
    }
    ++index;
  }
}

bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kMemberAccess ||
      expr->lhs->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view method = expr->lhs->rhs->text;
  auto entry = std::ranges::find_if(
      kCovergroupMethods, [&](const auto& m) { return m.first == method; });
  CovergroupInstance* inst = ctx.Covergroups().Find(expr->lhs->lhs->text, ctx);
  if (inst == nullptr || entry == kCovergroupMethods.end()) return false;
  out = entry->second(*inst, expr, ctx, arena);
  return true;
}

}  // namespace delta
