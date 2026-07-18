#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "simulator/coverage_types.h"

namespace delta {

class CoverageDB {
 public:
  CoverGroup* CreateGroup(std::string name);
  CoverGroup* FindGroup(std::string_view name);
  uint32_t GroupCount() const;

  static CoverPoint* AddCoverPoint(CoverGroup* group, std::string name);
  static CoverBin* AddBin(CoverPoint* cp, CoverBin bin);

  static void AutoCreateBins(CoverPoint* cp, int64_t min_val, int64_t max_val);

  static CrossCover* AddCross(CoverGroup* group, CrossCover cross);

  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values);

  static double GetCoverage(const CoverGroup* group);
  static double GetInstCoverage(const CoverGroup* group);
  static double GetPointCoverage(const CoverPoint* cp);
  static double GetCrossCoverage(const CrossCover* cross);

  // Overall coverage of all coverage group types, as a real number in the
  // range 0 to 100. This is the value returned by the $get_coverage() system
  // function (LRM 19.9); the underlying computation is the coverage average of
  // LRM 19.11.
  double GetGlobalCoverage() const;

  // --- LRM 19.9: predefined coverage system tasks and system functions ------

  // $set_coverage_db_name(filename) records the file name of the coverage
  // database into which coverage information is written at the end of a
  // simulation run (LRM 19.9). A later call replaces the recorded name.
  void SetCoverageDbName(std::string filename);
  const std::string& CoverageDbName() const;

  // $load_coverage_db(filename) loads cumulative coverage information for all
  // coverage group types (LRM 19.9). This applies the loaded snapshot to the
  // live database: for a covergroup type that already exists, the loaded bin
  // hit counts and sample count accumulate onto the live ones (matching
  // coverpoints, crosses, and bins by name); a coverpoint, cross, or bin found
  // only in the loaded data is appended; a covergroup type absent from the live
  // database is added in full.
  void MergeCumulativeCoverage(const std::vector<CoverGroup>& cumulative);

  // Reads a persisted coverage snapshot from `path` and applies it to the live
  // database through MergeCumulativeCoverage, which is the load half of
  // $load_coverage_db (LRM 19.9). Returns false when the file cannot be opened
  // or its contents are malformed, leaving the live database unchanged in the
  // open-failure case. The serialized form is line-oriented tokens: "CG <name>
  // <sample_count>" opens a covergroup type, "CP <name>" a coverpoint within
  // it, and "BIN <name> <value> <hit_count>" a bin within that coverpoint.
  bool LoadCoverageDbFile(const std::string& path);

  // --- LRM 19.8: predefined coverage methods --------------------------------

  // start()/stop() control whether the instance collects coverage. While
  // stopped, a triggered sample() records neither a sampling event nor any bin
  // hit (LRM 19.8).
  static void Start(CoverGroup* group);
  static void Stop(CoverGroup* group);

  // set_inst_name() assigns the instance name procedurally (LRM 19.8). The
  // instance name is the per-instance option.name of LRM 19.10.
  static void SetInstName(CoverGroup* group, std::string name);

  // The optional ref-int pair of get_coverage()/get_inst_coverage() reports the
  // number of covered bins and the number of coverage bins defined for the
  // item. For a covergroup the counts are aggregated over all coverpoints and
  // crosses; for a coverpoint or cross they are the numerator and denominator
  // of the (unscaled) coverage value (LRM 19.8).
  static double GetCoverage(const CoverGroup* group, int32_t& covered_bins,
                            int32_t& total_bins);
  static double GetInstCoverage(const CoverGroup* group, int32_t& covered_bins,
                                int32_t& total_bins);

  // --- LRM 19.6: cross coverage ---------------------------------------------

  // Ensures a coverpoint exists for every name listed in a cross. When a bare
  // variable is crossed, an implicit coverpoint is created for it as though it
  // had been declared with "coverpoint <var>;" (LRM 19.6).
  static void EnsureCrossCoverPoints(CoverGroup* group,
                                     const std::vector<std::string>& names);

  // True when every cross item resolves to a coverpoint defined in the same
  // covergroup. Crossing items from another covergroup is illegal (LRM 19.6).
  static bool CrossItemsInSameGroup(const CoverGroup* group,
                                    const std::vector<std::string>& names);

  // Builds the cross bins as the Cartesian product of the constituent
  // coverpoints' bins. Default, ignore, and illegal coverpoint bins do not
  // contribute any cross product (LRM 19.6).
  static void AutoCreateCrossBins(CoverGroup* group, CrossCover* cross);

  // A bare variable crossed directly must be integral. A real value can only
  // participate in a cross through an explicitly declared coverpoint of a real
  // expression (LRM 19.6).
  static bool CrossBareVariableAllowed(bool variable_is_real);

  // --- LRM 19.6.1: defining cross coverage bins -----------------------------

  // binsof yields the bins of its expression. With bin_index < 0 the argument
  // is a coverpoint (binsof(cp)) and every bin of the coverpoint is yielded;
  // with bin_index >= 0 the argument is a single coverpoint bin
  // (binsof(cp.bin)) and only that one bin is yielded. The yielded bins are
  // returned as their associated value sets (LRM 19.6.1).
  static std::vector<std::vector<int64_t>> BinsofYield(const CoverPoint* cp,
                                                       int64_t bin_index = -1);

  // From a coverpoint's bins (given as their value sets), selects those whose
  // associated values intersect the desired value set: the inclusion form
  // "binsof(x) intersect {y}". With negate, selects the bins whose values do
  // not intersect, i.e. "! binsof(x) intersect {y}". Returns the indices of the
  // selected bins (LRM 19.6.1).
  static std::vector<size_t> SelectBinsByIntersect(
      const std::vector<std::vector<int64_t>>& bins,
      const std::vector<int64_t>& values, bool negate);

  // Enumerates the cross products of a cross whose coverpoints have the given
  // bin counts: the Cartesian product of bin indices, one index per coverpoint.
  // Each product is the tuple of chosen bin indices. A coverpoint with no bins
  // yields no products (LRM 19.6.1).
  static std::vector<std::vector<size_t>> EnumerateCrossProducts(
      const std::vector<size_t>& per_point_bin_counts);

  // The cross products a single-coverpoint select expression denotes within a
  // cross: those whose chosen bin at coverpoint `point` is one of
  // `selected_point_bins` (the bins kept by SelectBinsByIntersect). The other
  // coverpoints range over all of their bins (LRM 19.6.1).
  static std::vector<std::vector<size_t>> SelectProductsByPointBins(
      const std::vector<size_t>& per_point_bin_counts, size_t point,
      const std::vector<size_t>& selected_point_bins);

  // Combines two cross-product selections with the logical && operator: the
  // products present in both selections (LRM 19.6.1).
  static std::vector<std::vector<size_t>> AndCrossSelections(
      const std::vector<std::vector<size_t>>& lhs,
      const std::vector<std::vector<size_t>>& rhs);

  // Combines two cross-product selections with the logical || operator: the
  // products present in either selection, without duplication (LRM 19.6.1).
  static std::vector<std::vector<size_t>> OrCrossSelections(
      const std::vector<std::vector<size_t>>& lhs,
      const std::vector<std::vector<size_t>>& rhs);

  // The automatically generated cross products retained alongside a set of
  // user-defined cross bins. By default (cross_retain_auto_bins true) an auto
  // bin is retained for each cross product not selected by any user-defined
  // cross bin; when the option is false none are retained (LRM 19.6.1).
  static std::vector<std::vector<size_t>> RetainedAutoCrossProducts(
      const std::vector<size_t>& per_point_bin_counts,
      const std::vector<std::vector<size_t>>& user_selected_products,
      bool retain_auto_bins);

  // --- LRM 19.6.1.1: select expressions on transition bins ------------------

  // The value set a select expression's binsof operator intersects against for
  // one bin. An ordinary value bin contributes its values directly; for a
  // transition bin binsof uses the last value of each transition sequence the
  // bin carries (LRM 19.6.1.1), since a transition has no single value of its
  // own. Returns an empty set for a transition bin that carries no sequence.
  static std::vector<int64_t> BinsofBinValues(const CoverBin& bin);

  // --- LRM 19.6.1.2: cross bin with covergroup expressions ------------------

  // Counts how many value tuples of a candidate bin tuple satisfy the
  // with_covergroup_expression. The candidate bin tuple is given as one value
  // set per coverpoint; its value tuples are the Cartesian product of those
  // sets. The predicate receives one value tuple at a time — the value each
  // cross_item takes in that tuple — because the cross_items occurring in the
  // with_covergroup_expression stand for those per-tuple values (LRM 19.6.1.2).
  static uint64_t CountSatisfyingValueTuples(
      const std::vector<std::vector<int64_t>>& bin_tuple_value_sets,
      const std::function<bool(const std::vector<int64_t>&)>& pred);

  // Selects, from a list of candidate bin tuples, those a select_expression
  // keeps. Each candidate is one value set per coverpoint. When pred is null
  // the select_expression is a bare cross_identifier, which selects every
  // candidate bin tuple. When pred is given (a with clause) a candidate is kept
  // only when its satisfying value tuple count meets the matches policy: every
  // value tuple for the $ form (require_all), otherwise at least min_count,
  // which is one when no matches clause was written. Returns the indices of the
  // kept candidates, in order (LRM 19.6.1.2).
  static std::vector<size_t> SelectCrossBinTuples(
      const std::vector<std::vector<std::vector<int64_t>>>&
          candidate_bin_tuples,
      const std::function<bool(const std::vector<int64_t>&)>* pred,
      const CrossWithMatchPolicy& policy);

  // Selects, from a list of candidate bin tuples, those a cross_set_expression
  // keeps. A cross_set_expression yields a queue of the cross's CrossQueueType,
  // each element a value tuple of type CrossValType — one component per
  // coverpoint of the cross (LRM 19.6.1.3). A candidate bin tuple's value tuple
  // is "present in the cross_set_expression" when it equals one of the queue's
  // elements. Selection is subject to the same matches policy as the with
  // covergroup expression (LRM 19.6.1.2): the policy counts, per candidate, how
  // many of its value tuples are present in the queue, keeping the candidate
  // when every value tuple is present for the $ form (require_all), otherwise
  // when at least min_count are — which is one when no matches clause is
  // written, the default policy where a single value tuple of the bin tuple
  // present in the queue selects it. Returns the kept candidate indices, in
  // order (LRM 19.6.1.4).
  static std::vector<size_t> SelectCrossBinTuplesBySetExpression(
      const std::vector<std::vector<std::vector<int64_t>>>&
          candidate_bin_tuples,
      const std::vector<std::vector<int64_t>>& set_expression_elements,
      const CrossWithMatchPolicy& policy);

  // --- LRM 19.6.2: excluding cross products ---------------------------------

  // Excludes from coverage every cross product an ignore_bins select expression
  // selects. The select expression has already been evaluated to its set of
  // cross products by the LRM 19.6.1 machinery; this removes those products
  // from a given set, so that all cross products satisfying the select
  // expression are excluded from coverage. Each cross product is a tuple of
  // chosen bin indices, one per coverpoint. The surviving products keep their
  // original order (LRM 19.6.2).
  static std::vector<std::vector<size_t>> ExcludeIgnoredCrossProducts(
      const std::vector<std::vector<size_t>>& products,
      const std::vector<std::vector<size_t>>& ignored);

  // Whether a cross product selected by an ignore_bins select expression is
  // still retained when some other cross coverage bin of the same cross
  // includes it. Ignored cross products are excluded even if they are included
  // in another cross coverage bin of the enclosing cross, so this always
  // returns false regardless of the other-bin membership (LRM 19.6.2).
  static bool IgnoredCrossProductRetained(bool also_in_other_cross_bin);

  // --- LRM 19.6.3: specifying illegal cross products ------------------------

  // Excludes from coverage every cross product an illegal_bins select
  // expression selects. The select expression has already been evaluated to its
  // set of cross products by the LRM 19.6.1 machinery; this removes those
  // products from a given set, exactly as the ignore_bins case does, so that
  // all cross products satisfying the select expression are excluded from
  // coverage. Each cross product is a tuple of chosen bin indices, one per
  // coverpoint; the surviving products keep their original order (LRM 19.6.3).
  static std::vector<std::vector<size_t>> ExcludeIllegalCrossProducts(
      const std::vector<std::vector<size_t>>& products,
      const std::vector<std::vector<size_t>>& illegal);

  // Classifies a sampled cross product against the cross's illegal_bins and
  // ignore_bins product sets and whether some other cross coverage bin of the
  // enclosing cross also includes it. A product selected by illegal_bins is
  // excluded from coverage and raises a run-time error; this takes precedence
  // over any other treatment, so the error is raised even when the same product
  // is also named by an ignore_bins select expression or included in another
  // cross bin. A product that is only ignored is excluded with no error.
  // Anything else is counted toward its cross product bin (LRM 19.6.3).
  static CrossSampleOutcome ClassifyCrossSample(
      const std::vector<size_t>& product,
      const std::vector<std::vector<size_t>>& illegal,
      const std::vector<std::vector<size_t>>& ignored,
      bool also_in_other_cross_bin);

  // --- LRM 19.5.1: specifying bins for values -------------------------------

  // Distributes a covergroup_range_list's items across a fixed number of bins.
  // B = floor(total / num_bins), but not less than 1; the first B items go to
  // the first bin, the next B to the next, and so on, with the last bin
  // absorbing any remainder. Duplicate items are retained, so the same value
  // can land in more than one bin. When num_bins exceeds the item count, the
  // trailing bins are left empty. The same distribution applies to a real
  // coverpoint, whose items are the intervals of its ranges plus its individual
  // values (LRM 19.5.1).
  static std::vector<std::vector<int64_t>> DistributeValues(
      const std::vector<int64_t>& values, uint32_t num_bins);

  // Names one element of an integral state bin array. For an open array
  // "name[]" the argument is the matched value, so names read "name[value]";
  // for a sized array "name[N]" it is the ordinal position, ranging from 0
  // through N-1 (LRM 19.5.1).
  static std::string StateBinName(std::string_view base, int64_t index);

  // Builds the open-array integral bins for "name[]": one bin per distinct
  // value of the range list, named "name[value]". A value listed more than once
  // (e.g. via overlapping ranges) still yields a single bin; first-occurrence
  // order is preserved (LRM 19.5.1).
  static std::vector<CoverBin> OpenArrayValueBins(
      std::string_view base, const std::vector<int64_t>& values);

  // Partitions a real range [low, high] into intervals of the given real
  // interval size. A range no wider than one interval yields a single inclusive
  // interval; a wider range is split into interval-size partitions, the last of
  // which may be shorter and is inclusive of high. A range bounded with the $
  // primary is never divided and always yields a single bin (LRM 19.5.1).
  static std::vector<RealInterval> RealRangeIntervals(double low, double high,
                                                      double interval,
                                                      bool uses_dollar);

  // Names a real interval bin. A square bracket denotes an inclusive endpoint,
  // a parenthesis an exclusive one (LRM 19.5.1).
  static std::string RealIntervalBinName(std::string_view base,
                                         const RealInterval& interval);

  // Names a real bin covering a single individual value (LRM 19.5.1).
  static std::string RealValueBinName(std::string_view base, double value);

  // Merges intervals that are exactly identical when an open real bin array
  // spans several ranges. Two intervals merge only when both endpoints and
  // their inclusivity agree; intervals that share endpoints but differ in
  // inclusivity are kept separate (LRM 19.5.1).
  static std::vector<RealInterval> MergeIdenticalIntervals(
      const std::vector<RealInterval>& intervals);

  // A default bin for a real coverpoint cannot be an array of bins: neither the
  // [] form nor the [N] form is allowed (LRM 19.5.1).
  static bool RealDefaultBinMayBeArray();

  // Converts a tolerance specification attached to a single real value into the
  // inclusive real range it denotes. The +/- token gives an absolute tolerance,
  // yielding [value - tol, value + tol]; the +%- token gives a relative
  // tolerance expressed as a percentage, yielding
  // [value - |value|*tol/100, value + |value|*tol/100]. The tolerance is a
  // magnitude. Because the result is a range, the range/interval rules apply:
  // feeding it to RealRangeIntervals divides a tolerance range wider than the
  // real interval into multiple bins (LRM 19.5.1).
  static std::pair<double, double> ToleranceRange(double value,
                                                  double tolerance,
                                                  bool is_percent);

  // --- LRM 19.5.1.1: coverpoint bin "with" expressions ----------------------

  // Selects the candidate values for which the per-value predicate is true.
  // The predicate receives each candidate (the "item" of the with expression).
  // Order and duplicate values are preserved (LRM 19.5.1.1).
  static std::vector<int64_t> ApplyWithExpression(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred);

  // Applies a with expression and distributes the values into num_bins bins.
  // By default the filter runs before distribution; distribute_first (a
  // covergroup type option, LRM 19.7.1) runs distribution first and filters the
  // contents of each resulting bin (LRM 19.5.1.1).
  static std::vector<std::vector<int64_t>> ApplyWithAndDistribute(
      const std::vector<int64_t>& candidates,
      const std::function<bool(int64_t)>& pred, uint32_t num_bins,
      bool distribute_first);

  // A with bin filter is illegal on a coverpoint of a real type (LRM 19.5.1.1).
  static bool WithExpressionAllowed(const CoverPoint* cp);

  // In place of an explicit range list, a with expression may name the
  // enclosing coverpoint to denote all of its values; no other coverpoint name
  // is permitted (LRM 19.5.1.1).
  static bool WithRangeReferenceAllowed(std::string_view self_name,
                                        std::string_view referenced_name);

  // --- LRM 19.5.1.2: coverpoint bin set covergroup expressions --------------

  // The set_covergroup_expression that defines a bin's values is evaluated
  // once, when the covergroup instance is constructed, rather than being
  // re-evaluated at each sampling point. Given how many times the instance is
  // sampled after construction, returns how many times the set expression is
  // evaluated, which is always one and independent of the sample count
  // (LRM 19.5.1.2).
  static uint64_t SetExpressionEvaluationCount(uint64_t sample_count);

  // --- LRM 19.5.2: specifying bins for transitions --------------------------

  // A trans_list specifies ordered integral value transitions of the coverage
  // point; transition bins of a real coverpoint are not allowed (LRM 19.5.2).
  static bool TransitionBinAllowed(const CoverPoint* cp);

  // A transition bin specification must describe at least one transition, i.e.
  // two successive sample points. A specification of "length 0" — a single
  // value range, or a single value range whose repeat_range evaluates to 1 —
  // is illegal. Returns true when the spec spans at least two sample points
  // (LRM 19.5.2).
  static bool TransitionLengthLegal(size_t sample_points);

  // Expands a set transition such as "range_list1 => range_list2" into the
  // individual ordered transitions it denotes. Each step is the list of values
  // permitted at that sample point; the result is the Cartesian product taken
  // in order, so {{1,5},{6,7}} yields 1=>6, 1=>7, 5=>6, 5=>7 (LRM 19.5.2).
  static std::vector<std::vector<int64_t>> ExpandSetTransition(
      const std::vector<std::vector<int64_t>>& steps);

  // Expands a consecutive repetition "item [* lo:hi]" into one concrete
  // sequence per repetition count in [lo, hi]: the item's values are repeated
  // n times for each n. A single count (lo == hi) yields a single sequence;
  // e.g. {3} [*3:5] yields 3=>3=>3, 3=>3=>3=>3 and 3=>3=>3=>3=>3 (LRM 19.5.2).
  static std::vector<std::vector<int64_t>> ExpandConsecutiveRepeat(
      const std::vector<int64_t>& item, uint32_t lo, uint32_t hi);

  // Names one element of a transition bin array declared as "name[]". The bin
  // name embeds the bounded transition it matched, e.g. "name[4=>5=>6]"
  // (LRM 19.5.2).
  static std::string TransitionArrayBinName(
      std::string_view base, const std::vector<int64_t>& transition);

  // A consecutive repetition has a determined length; the goto and
  // nonconsecutive repetitions vary in length and are therefore unbounded
  // (LRM 19.5.2).
  static bool TransitionRepeatBounded(TransitionRepeatKind kind);

  // Transitions of unbounded or undetermined varying length cannot be used with
  // the multiple bins construct (the "[]" notation); attempting to do so is an
  // error. Returns true only when the transition sequence has a bounded length
  // (LRM 19.5.2).
  static bool MultipleBinsAllowsTransition(bool sequence_bounded);

  // A default sequence specification does not accept multiple transition bins:
  // the "[]" notation is not allowed on it (LRM 19.5.2).
  static bool DefaultSequenceAllowsMultipleBins();

  // A default sequence transition bin is incremented for a sample only when no
  // other nondefault transition bin of the coverpoint increments on that sample
  // and none of the coverpoint's previously pending transition sequences
  // remains pending (LRM 19.5.2).
  static bool DefaultSequenceTransitionIncrements(
      bool any_nondefault_incremented, bool any_pending);

  // --- LRM 19.5.3: automatic bin creation for integral coverage points ------

  // Bins are created automatically only for a coverpoint of an integral
  // expression. A real coverpoint never receives automatically created bins, so
  // this returns false for a real coverpoint (LRM 19.5.3).
  static bool AutoBinsAllowed(const CoverPoint* cp);

  // Automatic state bins are created only when an integral coverpoint defines
  // no bins other than ignore or illegal bins. A coverpoint that already
  // carries an explicit, wildcard, transition, or default user bin suppresses
  // automatic bin creation; ignore and illegal bins do not, because they only
  // subtract from — never define — the covered value set (LRM 19.5.3). Returns
  // true when the coverpoint is eligible for automatic bin creation.
  static bool ShouldAutoCreateBins(const CoverPoint* cp);

  // Number of automatic bins N for a non-enumeration integral coverpoint: the
  // minimum of 2^M (M is the number of bits needed to represent the coverpoint)
  // and the auto_bin_max option in effect. This same N is the denominator of
  // the automatic-bin coverpoint coverage, MIN(auto_bin_max, 2^M)
  // (LRM 19.11.1), so the two subclauses share this count.
  static uint64_t AutoBinCount(uint32_t coverpoint_bits, uint64_t auto_bin_max);

  // Number of automatic bins for an enumeration coverpoint: one bin per
  // enumeration member, i.e. the cardinality of the enumeration. The
  // auto_bin_max limit does not apply to an enumeration coverpoint
  // (LRM 19.5.3).
  static uint64_t AutoBinCountEnum(uint64_t enum_cardinality);

  // A sampled value is collected into an automatic bin only when it is a
  // 2-state value; a value containing x or z is excluded. Returns true when a
  // sample with the given unknown-bit status is eligible for an automatic bin
  // (LRM 19.5.3).
  static bool AutoBinSampleIncluded(bool sample_has_xz);

  // Name of an automatically created bin: "auto[value]" when the bin holds a
  // single coverage point value (low == high) and "auto[low:high]" when it
  // spans a range of values (LRM 19.5.3).
  static std::string AutoBinName(int64_t low, int64_t high);

  // Name of an automatically created bin of an enumeration coverpoint. The name
  // embeds the named constant associated with the enumerated value rather than
  // a numeric value: "auto[NAME]" (LRM 19.5.3).
  static std::string AutoEnumBinName(std::string_view constant_name);

  // --- LRM 19.5.4: wildcard specification of coverage point bins ------------

  // Expands a wildcard value pattern into the concrete 2-state values it
  // matches. In a wildcard bin every x, z, or ? bit position is a wildcard that
  // matches both 0 and 1; the remaining bits must match exactly. The fixed bits
  // are supplied as `pattern` and marked by the set bits of `care_mask` (a set
  // mask bit denotes a fixed position); the cleared mask bits within `width`
  // are the wildcards. The result enumerates every value obtained by filling
  // the wildcard positions with all combinations of 0 and 1, e.g. 4'b11??
  // yields 12, 13, 14, 15 (LRM 19.5.4).
  static std::vector<int64_t> ExpandWildcardValue(int64_t pattern,
                                                  uint64_t care_mask,
                                                  uint32_t width);

  // A wildcard bin definition only considers 2-state values; a sampled value
  // that contains x or z is excluded from the wildcard comparison. Returns true
  // when a sample with the given unknown-bit status is eligible to be matched
  // against a wildcard bin (LRM 19.5.4).
  static bool WildcardSampleIncluded(bool sample_has_xz);

  // Wildcard specification of coverpoint bins of a real type is not allowed.
  // Returns false for a real coverpoint, mirroring the other bin-legality
  // queries (LRM 19.5.4).
  static bool WildcardBinsAllowed(const CoverPoint* cp);

  // --- LRM 19.5.5: excluding coverage point values or transitions -----------

  // Removes every value named by an ignore_bins state set from a coverage bin's
  // value set. Each occurrence of an ignored value is dropped; values not
  // ignored keep their order. Per LRM 19.5.5 this removal is performed only
  // after values have been distributed to the specified bins, so it is applied
  // to a bin's already-populated value set (LRM 19.5.5).
  static std::vector<int64_t> RemoveIgnoredValues(
      const std::vector<int64_t>& bin_values,
      const std::vector<int64_t>& ignored_values);

  // True when a covered transition sequence must be excluded because it cannot
  // be matched without also matching an ignored transition sequence — that is,
  // when the ignored sequence occurs as a contiguous subsequence of the covered
  // one (ignoring 2=>3 removes the covered 1=>2=>3=>4) (LRM 19.5.5).
  static bool CoveredTransitionIsIgnored(const std::vector<int64_t>& covered,
                                         const std::vector<int64_t>& ignored);

  // An ignored individual value has no effect on a transition that includes the
  // value: a transition bin is never removed merely because its sequence passes
  // through an ignored state value. Always false (LRM 19.5.5).
  static bool IgnoredValueAffectsTransition(
      int64_t ignored_value, const std::vector<int64_t>& transition);

  // An ignore_bins transition specification cannot describe a sequence of
  // unbounded or undetermined varying length; it is legal only when the
  // sequence has a bounded (determined) length (LRM 19.5.5).
  static bool IgnoreTransitionLengthLegal(bool sequence_bounded);

  // --- LRM 19.5.6: specifying illegal coverage point values or transitions ---

  // Removes every value named by an illegal_bins state set from a coverage
  // bin's value set. Each occurrence of an illegal value is dropped; the
  // remaining values keep their relative order. Like the ignore case, this
  // removal is performed only after values have been distributed to the
  // specified bins, so it acts on an already-populated value set (LRM 19.5.6).
  static std::vector<int64_t> RemoveIllegalValues(
      const std::vector<int64_t>& bin_values,
      const std::vector<int64_t>& illegal_values);

  // True when a covered transition sequence must be excluded because it cannot
  // be matched without also matching an illegal transition sequence — that is,
  // when the illegal sequence occurs as a contiguous subsequence of the covered
  // one (an illegal 2=>3 removes the covered 1=>2=>3=>4) (LRM 19.5.6).
  static bool CoveredTransitionIsIllegal(const std::vector<int64_t>& covered,
                                         const std::vector<int64_t>& illegal);

  // Specifying an illegal individual value has no effect on a transition that
  // includes the value: a transition bin is never removed merely because its
  // sequence passes through an illegal state value. Always false (LRM 19.5.6).
  static bool IllegalValueAffectsTransition(
      int64_t illegal_value, const std::vector<int64_t>& transition);

  // An illegal_bins transition specification cannot describe a sequence of
  // unbounded or undetermined varying length; it is legal only when the
  // sequence has a bounded (determined) length (LRM 19.5.6).
  static bool IllegalTransitionLengthLegal(bool sequence_bounded);

  // Illegal bins take precedence over any other bins: a value or transition
  // that hits an illegal bin raises a run-time error even when it is also
  // included in another (legal) bin. Always true (LRM 19.5.6).
  static bool IllegalTakesPrecedence(bool also_in_other_bin);

  // --- LRM 19.5.7: value resolution -----------------------------------------

  // Effective type of the coverpoint expression e that bin values are resolved
  // against. With an explicit coverpoint cast type the effective type is that
  // type; with no coverpoint type it is the self-determined type of e
  // (LRM 19.5.7 a). Enumeration operands are taken at their base type, which is
  // already reflected in the width/signedness supplied here.
  static CoverpointEffectiveType EffectiveCoverpointType(
      bool has_coverpoint_type, CoverpointEffectiveType coverpoint_type,
      CoverpointEffectiveType self_determined_type);

  // Statically casts a bin value to the effective type of e: the value is
  // reduced to the type's width and reinterpreted as signed or unsigned. This
  // is the cast LRM 19.5.7 b requires before a bin value is compared with a
  // sampled value.
  static int64_t CastToEffectiveType(int64_t value,
                                     CoverpointEffectiveType eff);

  // Lowest and highest value expressible by an effective type — the closed
  // domain a bin value can occupy after the cast of LRM 19.5.7 b. A range bin
  // surviving warning resolution is the intersection of its values with this
  // domain (LRM 19.5.7, third range bullet).
  static int64_t EffectiveTypeMin(CoverpointEffectiveType eff);
  static int64_t EffectiveTypeMax(CoverpointEffectiveType eff);

  // Resolves one bin value b against the effective type of e and reports
  // whether and why a warning is issued. x and z bits of a wildcard bin are
  // treated as all 0 and 1 before this resolution, so a wildcard bin never
  // warns for unknown bits (LRM 19.5.7 preamble and condition 3).
  static BinValueResolution ResolveBinValue(int64_t value, bool value_is_signed,
                                            bool value_has_xz, bool is_wildcard,
                                            CoverpointEffectiveType eff);

  // Whether a singleton bin value participates in the bin: a singleton for
  // which a warning is issued does not participate (LRM 19.5.7, first warning
  // bullet).
  static bool SingletonValueParticipates(BinValueResolution resolution);

  // A bin range [low:high] as written in a bins specification (LRM 19.5.7,
  // range bullets). Each endpoint carries its value and whether it had x or z
  // bits, and `is_wildcard` records that the range belongs to a wildcard bin
  // whose unknown endpoint bits were resolved to 0/1 beforehand.
  struct BinRangeSpec {
    int64_t low = 0;
    int64_t high = 0;
    bool low_has_xz = false;
    bool high_has_xz = false;
    bool is_wildcard = false;
  };

  // Resolves a bin range [low:high] against the effective type of e, returning
  // the values that participate in the bin. The range drops out entirely when
  // an endpoint carries x or z bits or when every value in the range would
  // warn; otherwise it becomes the intersection of its values with the values
  // expressible by the effective type (LRM 19.5.7, second and third range
  // bullets). Wildcard endpoints' x/z bits are resolved beforehand and do not
  // force the range out.
  static std::vector<int64_t> ResolveBinRange(const BinRangeSpec& range,
                                              CoverpointEffectiveType eff);

  // --- LRM 19.7: instance coverage options ----------------------------------

  // A weight value supplied for the weight option shall be a non-negative
  // integral value (LRM 19.7, Table 19-1).
  static bool OptionWeightValid(int32_t weight);

  // Specifying a value for the same option more than once within a single
  // covergroup definition is an error (LRM 19.7). Given the options assigned in
  // definition order, returns true when any option appears more than once.
  static bool OptionSpecifiedMoreThanOnce(
      const std::vector<InstanceOptionKind>& assigned);

  // Table 19-2: whether an instance option may be specified at a given
  // syntactic level (LRM 19.7). All instance options may be set at the
  // covergroup level.
  static bool OptionAllowedAt(InstanceOptionKind kind,
                              CoverSyntacticLevel level);

  // When set at the covergroup level, every instance option acts as a default
  // for the corresponding option of the coverpoints and crosses, except weight,
  // goal, comment, and per_instance (LRM 19.7). The covergroup-only options
  // (name, get_inst_coverage) likewise do not propagate, as they cannot be set
  // at a lower level.
  static bool OptionDefaultsToLowerLevels(InstanceOptionKind kind);

  // per_instance and get_inst_coverage can only be set in the covergroup
  // definition; auto_bin_max, detect_overlap, and cross_retain_auto_bins can
  // only be set in the covergroup or coverpoint definition. The remaining
  // instance options can also be assigned procedurally after the covergroup has
  // been instantiated (LRM 19.7).
  static bool OptionSettableProcedurally(InstanceOptionKind kind);

  // --- LRM 19.7.1: covergroup type options ----------------------------------

  // Computes type (cumulative) coverage over the instances of a covergroup
  // type. With merge_instances false the per-instance coverage is combined as a
  // weighted average (LRM 19.11.3). With merge_instances true the bins of every
  // instance are unioned by name: same-named bins overlap and their hit counts
  // sum, while differently named bins are distinct members of the union, so
  // instances with different bin layouts enlarge it rather than collapse onto
  // one another (LRM 19.11.3).
  static double ComputeTypeCoverage(
      const std::vector<const CoverGroup*>& instances, bool merge_instances);

  // Table 19-4: whether a type option may be assigned at a given syntactic
  // level (LRM 19.7.1).
  static bool TypeOptionAllowedAt(TypeOptionKind kind,
                                  CoverSyntacticLevel level);

  // When set at the covergroup level, only real_interval acts as a default for
  // lower syntactic levels (LRM 19.7.1).
  static bool TypeOptionDefaultsToLowerLevels(TypeOptionKind kind);

  // strobe and real_interval may only be set in the covergroup definition; the
  // remaining type options may also be assigned procedurally (LRM 19.7.1).
  static bool TypeOptionSettableProcedurally(TypeOptionKind kind);

  // --- LRM 19.11: coverage computation --------------------------------------

  // True when the denominator Σ Wi of the covergroup coverage equation is zero:
  // the covergroup has no coverage items, every item weight is zero, or every
  // item is excluded by its own coverage rules (LRM 19.11). GetCoverage maps a
  // zero denominator to 0.0 or 100.0 depending on the covergroup's own weight.
  static bool CovergroupCoverageDenominatorZero(const CoverGroup* group);

  // Computes the $get_coverage value of a design: the weighted average of the
  // coverage of all covergroup instances. An instance whose own denominator is
  // zero does not contribute to the overall score. With no contributing
  // instance — none exist, or every covergroup weight is zero — the result is
  // 100.0 (LRM 19.11).
  static double ComputeOverallCoverage(
      const std::vector<const CoverGroup*>& instances);

  // --- LRM 19.11.1: coverpoint coverage computation -------------------------

  // True when a coverpoint's coverage denominator is zero: none of its bins has
  // an associated value or transition. A bin with neither is excluded from both
  // the numerator and the denominator, and a coverpoint left with no such bin
  // does not contribute to the covergroup coverage average (LRM 19.11.1).
  static bool PointCoverageDenominatorZero(const CoverPoint* cp);

  // The ref-int pair form of get_coverage()/get_inst_coverage() applied to a
  // coverpoint: reports the number of covered bins and the number of bins that
  // participate in the coverage (the numerator and denominator of the
  // coverpoint coverage). When the denominator is zero, zero is reported for
  // both counts (LRM 19.11.1).
  static double GetPointCoverage(const CoverPoint* cp, int32_t& covered_bins,
                                 int32_t& total_bins);

  // The hit-count threshold a bin must reach to be considered covered in
  // cumulative (type) coverage: the maximum of the at_least option values
  // across all instances, which is the more conservative choice. With no
  // instance values supplied the default at_least of 1 applies (LRM 19.11.1).
  static uint32_t CumulativeAtLeast(
      const std::vector<uint32_t>& at_least_values);

  // --- LRM 19.11.2: cross coverage computation ------------------------------

  // The number of automatically generated cross bins B_c of a cross. It is the
  // product of the bin cardinalities B_j of the crossed coverpoints — the total
  // number of cross products ∏ B_j — less the number of cross products B_b that
  // are comprised by user-defined cross bins, since those products are
  // accounted for by the user-defined bins rather than by auto-cross bins. A
  // crossed coverpoint with no bins makes the product, and therefore B_c, zero
  // (LRM 19.11.2).
  static uint64_t CrossAutoBinCount(
      const std::vector<uint64_t>& per_point_bin_counts,
      uint64_t user_defined_cross_products);

  // The denominator of the cross coverage equation, B_c + B_u, where B_c is the
  // number of auto-cross bins (CrossAutoBinCount) and B_u is the number of
  // significant user-defined cross bins — those that contribute toward
  // coverage. Cross bins arising from ignore_bins and illegal_bins select
  // expressions do not contribute and are excluded from B_u by the caller; only
  // counting cross bins are passed here (LRM 19.11.2).
  static uint64_t CrossCoverageDenominator(
      const std::vector<uint64_t>& per_point_bin_counts,
      uint64_t user_defined_cross_products, uint64_t significant_user_bins);

  // Whether a user-defined cross bin counts toward the significant user-defined
  // bin total B_u. A cross product selected by an ignore_bins or illegal_bins
  // select expression contributes no coverage bin, so only a counting outcome
  // (LRM 19.6.3) raises B_u; ignored and illegal outcomes do not (LRM 19.11.2,
  // definition of B_u).
  static bool CrossBinCountsTowardCoverage(CrossSampleOutcome outcome);

  // True when a cross's coverage denominator B_c + B_u is zero: the cross has
  // no auto-cross bins and no significant user-defined cross bins. Such a cross
  // does not contribute to the parent covergroup's coverage computation, and
  // its own get_coverage value depends only on its weight (LRM 19.11.2).
  static bool CrossCoverageDenominatorZero(const CrossCover* cross);

  // The ref-int pair form of get_coverage()/get_inst_coverage() applied to a
  // cross: reports the number of covered cross bins and the size of the cross
  // coverage denominator (the numerator and denominator of the cross coverage).
  // When the denominator is zero, zero is reported for both counts (LRM
  // 19.11.2).
  static double GetCrossCoverage(const CrossCover* cross, int32_t& covered_bins,
                                 int32_t& total_bins);

  // --- LRM 19.11.3: type coverage computation -------------------------------

  // The type coverage of a single coverpoint, computed across the instances of
  // its covergroup type. With merge_instances false it is the weighted average
  // of the coverpoint's coverage in each instance, weighted by the coverpoint's
  // own option.weight in that instance. With merge_instances true it is the
  // union of the coverpoint's bins across instances: bins that share a name
  // overlap and their hit counts sum, while differently named bins are distinct
  // members of the union (LRM 19.11.3).
  static double ComputePointTypeCoverage(
      const std::vector<const CoverPoint*>& instances, bool merge_instances);

  // The type coverage of a single cross, computed across the instances of its
  // covergroup type, by the same two rules as ComputePointTypeCoverage but
  // weighted by the cross's own option.weight and unioning cross bins by their
  // cross-product name (LRM 19.11.3).
  static double ComputeCrossTypeCoverage(
      const std::vector<const CrossCover*>& instances, bool merge_instances);

  // --- LRM 19.4.1: embedded covergroup inheritance --------------------------

  // When a derived covergroup defines a coverpoint whose name is identical to a
  // coverpoint in the base covergroup, that base coverpoint no longer
  // contributes to the coverage computation. Marks every base coverpoint whose
  // name appears among the derived covergroup's coverpoint names as excluded so
  // the covergroup average (LRM 19.11) drops it (LRM 19.4.1).
  static void ApplyDerivedCoverpointOverrides(
      CoverGroup* base,
      const std::vector<std::string>& derived_coverpoint_names);

  // Even when a base coverpoint no longer contributes, a cross in the base
  // covergroup that includes that coverpoint still contributes to the
  // computation — unless the derived covergroup defines a cross with the same
  // name, which overrides it. Marks only the base crosses whose names appear
  // among the derived covergroup's cross names as excluded; all other base
  // crosses keep contributing regardless of overridden coverpoints (LRM
  // 19.4.1).
  static void ApplyDerivedCrossOverrides(
      CoverGroup* base, const std::vector<std::string>& derived_cross_names);

  // For the purposes of get_coverage(), a derived covergroup and its base
  // covergroup are separate types; no aggregation occurs across them. Two
  // covergroup instances aggregate for type coverage only when they are the
  // same covergroup type, so a base type name and a derived type name never
  // aggregate (LRM 19.4.1).
  static bool CovergroupTypesAggregate(std::string_view type_a,
                                       std::string_view type_b);

 private:
  void SampleCoverPoint(CoverPoint* cp, int64_t value);
  void SampleCross(CrossCover* cross,
                   const std::vector<std::pair<std::string, int64_t>>& vals);

  std::deque<CoverGroup> groups_;
  std::unordered_map<std::string, size_t> name_index_;
  // Destination file for the coverage database, set by $set_coverage_db_name
  // and written at the end of the run (LRM 19.9).
  std::string coverage_db_name_;
};

}  // namespace delta
