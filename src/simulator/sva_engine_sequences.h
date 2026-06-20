#ifndef DELTA_SIMULATOR_SVA_ENGINE_SEQUENCES_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SEQUENCES_H_

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

std::string_view SeverityToString(AssertionSeverity sev);

enum class PropertyResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
  kPending,
};

struct SequenceAttempt {
  uint32_t position = 0;
  uint32_t delay_remaining = 0;
  uint32_t match_count = 0;
  bool completed = false;
  bool failed = false;
};

void AdvanceSequence(SequenceAttempt& sa);

enum class SvaSequenceKind : uint8_t {
  kDelay,
  kConsecutiveRepetition,
  kGotoRepetition,
  kNonConsecutiveRepetition,
};

struct SvaSequence {
  SvaSequenceKind kind = SvaSequenceKind::kDelay;
  uint32_t delay_cycles = 0;
  uint32_t rep_min = 0;
  uint32_t rep_max = 0;
  std::function<bool(uint64_t)> expr_check;
};

bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

// §16.9.2.1: an empty sequence match (e.g. a[*0]) spans zero clock ticks and is
// thus of length 0, so concatenating it with another sequence through the
// ##delay operator obeys a dedicated set of rules. Which operand of the
// concatenation is the empty match.
enum class EmptyConcatSide : uint8_t { kEmptyLeft, kEmptyRight };

// Outcome of concatenating an empty match with another sequence via ##n.
struct EmptyConcatResult {
  // false records that "(empty ##0 seq)" and "(seq ##0 empty)" do not result in
  // a match; true means the concatenation collapses onto the surviving operand.
  bool matchable = false;
  // The ##(n-1) delay carried onto the surviving operand. Because the empty
  // operand occupies zero ticks, concatenating across it spends one tick fewer
  // than the written delay — the same reason an empty case (a[*0]) runs one
  // tick shorter than the corresponding length-1 case (a[*1]).
  uint32_t effective_delay = 0;
  // "(seq ##n empty)" trails the surviving sequence with `true, extending the
  // match one tick past seq's end; the empty-on-the-left rule does not.
  bool append_true = false;
};

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay);

// §16.9.2.1: a sequence admitting both empty and nonempty matches — a
// repetition whose count range spans zero, e.g. a[*0:1] — is evaluated by
// rewriting it as the OR of its empty case (count 0) and its nonempty cases
// (count >= 1). The composite matches when either disjunct matches; a range
// that excludes zero has only the nonempty case.
bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match);

bool EvalSequenceAnd(bool a_match, bool b_match);

// §16.9.5: the composite `e1 and e2` requires both operands to match. The
// operands begin at the same time, but their matches can complete at different
// times; once one operand matches it waits for the other, so the composite
// match completes at the later of the two operand end times. This carries the
// end-time alongside the match decision that EvalSequenceAnd reports.
struct SequenceAndMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time);

bool EvalSequenceOr(bool a_match, bool b_match);

// §16.9.7: `e1 or e2` matches whenever at least one operand matches. Unlike
// `and` and `intersect`, the operand matches are not fused into a single
// composite match: every match of either operand is, by itself, a match of the
// composite, and it ends exactly where that operand's match ends. The
// composite's match set is therefore the union of the two operands' match sets,
// so an `or` can yield several matches — including two ending on the same clock
// tick when both operands match there. This carries that union of end-times
// alongside the match decision that EvalSequenceOr reports.
struct SequenceOrMatches {
  bool matched = false;
  std::vector<uint32_t> end_times;
};
SequenceOrMatches EvalSequenceOrMatches(
    const std::vector<uint32_t>& a_end_times,
    const std::vector<uint32_t>& b_end_times);

// §16.9.8: first_match(seq) starts an evaluation attempt of the operand seq at
// the same clock tick and reduces seq's possibly-many matches to the ones that
// end earliest, discarding all subsequent matches. When seq has no match,
// first_match(seq) has none either. Otherwise the operand match(es) with the
// earliest ending clock tick are the matches of first_match(seq); every
// later-ending match is dropped. When more than one operand match shares that
// earliest ending tick, all of them are kept. This carries the surviving
// end-times alongside the match decision.
struct FirstMatchMatches {
  bool matched = false;
  std::vector<uint32_t> end_times;
};
FirstMatchMatches EvalFirstMatch(
    const std::vector<uint32_t>& operand_end_times);

bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

// §16.9.10: the containment `seq1 within seq2` is an abbreviation for
// (1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect seq2. The composite matches along a
// finite interval of consecutive clock ticks when seq2 matches along the whole
// interval and seq1 matches along some subinterval of it. Both operands shall
// therefore match, and the match of seq1 shall be contained in the match of
// seq2: seq1 shall start no earlier than seq2 starts and shall complete no
// later than seq2 completes. The intersection forces the composite to span
// seq2's interval, so the containment completes at seq2's match point. This
// carries the composite end-time alongside the match decision.
struct SequenceWithinMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceWithinMatch EvalSequenceWithin(bool inner_match, uint32_t inner_start,
                                       uint32_t inner_end, bool outer_match,
                                       uint32_t outer_start,
                                       uint32_t outer_end);

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_SEQUENCES_H_
