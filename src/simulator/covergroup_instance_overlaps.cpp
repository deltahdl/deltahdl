#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <format>
#include <iterator>
#include <map>
#include <set>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance_internal.h"

namespace delta {

namespace {

using BinPair = std::pair<size_t, size_t>;

// The pairs of bins two of `spans` share a value of, each pair once and the
// lower index first, where each span comes with the index of its bin, `low`
// gives a span's low end and `reaches(held, next)` whether a span reaches the
// low end of one starting no lower. The spans are swept in order of their low
// ends, each meeting the spans still open, so an array of single-value bins
// costs no comparison of its own.
template <typename Span, typename Low, typename Reaches>
std::set<BinPair> SweepOverlaps(std::vector<std::pair<Span, size_t>> spans,
                                Low low, Reaches reaches) {
  std::ranges::sort(spans, {},
                    [&low](const auto& span) { return low(span.first); });
  std::set<BinPair> pairs;
  std::vector<std::pair<Span, size_t>> open;
  for (const auto& [span, bin] : spans) {
    std::erase_if(open, [&reaches, &span](const auto& held) {
      return !reaches(held.first, span);
    });
    for (const auto& held : open) {
      if (held.second != bin) pairs.insert(std::minmax(held.second, bin));
    }
    open.emplace_back(span, bin);
  }
  return pairs;
}

// §19.7, Table 19-1: the pairs of `bins`' bins of the `bins` keyword whose
// range lists share a value: an integral coverpoint's values and ranges, or a
// real coverpoint's intervals (§19.5.1), whose high end is in the interval
// only where it is inclusive.
std::set<BinPair> RangeListOverlaps(const std::deque<CoverBin>& bins) {
  std::vector<std::pair<CoverValueRange, size_t>> spans;
  std::vector<std::pair<RealInterval, size_t>> intervals;
  for (size_t i = 0; i < bins.size(); ++i) {
    if (bins[i].kind != CoverBinKind::kExplicit) continue;
    for (const CoverValueRange& r : bins[i].ranges) spans.emplace_back(r, i);
    for (int64_t v : bins[i].values) {
      spans.emplace_back(CoverValueRange{v, v}, i);
    }
    for (const RealInterval& iv : bins[i].real_intervals) {
      intervals.emplace_back(iv, i);
    }
  }
  std::set<BinPair> pairs = SweepOverlaps(
      std::move(spans), [](const CoverValueRange& r) { return r.lo; },
      [](const CoverValueRange& held, const CoverValueRange& next) {
        return held.hi >= next.lo;
      });
  pairs.merge(SweepOverlaps(
      std::move(intervals), [](const RealInterval& iv) { return iv.low; },
      [](const RealInterval& held, const RealInterval& next) {
        return held.high > next.low ||
               (held.high_inclusive && held.high == next.low);
      }));
  return pairs;
}

// §19.7, Table 19-1: the pairs of `bins`' transition bins of the `bins`
// keyword whose transition lists share a transition, each pair once and the
// lower index first.
std::set<BinPair> TransitionListOverlaps(const std::deque<CoverBin>& bins) {
  std::map<std::vector<int64_t>, std::set<size_t>> holders;
  for (size_t i = 0; i < bins.size(); ++i) {
    if (bins[i].kind != CoverBinKind::kTransition) continue;
    for (const auto& sequence : bins[i].transitions)
      holders[sequence].insert(i);
  }
  std::set<BinPair> pairs;
  for (const auto& [sequence, held] : holders) {
    for (auto a = held.begin(); a != held.end(); ++a) {
      for (auto b = std::next(a); b != held.end(); ++b) pairs.insert({*a, *b});
    }
  }
  return pairs;
}

// §19.7, Table 19-1: the warning detect_overlap asks for, one per pair of
// `cp`'s bins in `pairs`, at the definition of the later bin of the pair,
// `origins` giving each bin's definition. `lists` names what overlaps.
void WarnOfOverlaps(const CoverPoint& cp, const std::set<BinPair>& pairs,
                    std::string_view lists,
                    const std::vector<SourceLoc>& origins, DiagEngine& diag) {
  for (const auto& [first, second] : pairs) {
    diag.Warning(
        origins[second],
        std::format("bins '{}' and '{}' of coverpoint '{}' overlap "
                    "in their {} lists",
                    cp.bins[first].name, cp.bins[second].name, cp.name, lists),
        Subclause("19.7"));
  }
}

}  // namespace

void WarnOfBinOverlaps(const CoverPoint& cp,
                       const std::vector<SourceLoc>& origins,
                       DiagEngine& diag) {
  WarnOfOverlaps(cp, RangeListOverlaps(cp.bins), "range", origins, diag);
  WarnOfOverlaps(cp, TransitionListOverlaps(cp.bins), "transition", origins,
                 diag);
}

}  // namespace delta
