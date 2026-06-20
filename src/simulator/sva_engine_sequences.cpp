#include "simulator/sva_engine_sequences.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

namespace delta {

std::string_view SeverityToString(AssertionSeverity sev) {
  switch (sev) {
    case AssertionSeverity::kInfo:
      return "INFO";
    case AssertionSeverity::kWarning:
      return "WARNING";
    case AssertionSeverity::kError:
      return "ERROR";
    case AssertionSeverity::kFatal:
      return "FATAL";
  }
  return "ERROR";
}

void AdvanceSequence(SequenceAttempt& sa) {
  if (sa.delay_remaining > 0) {
    --sa.delay_remaining;
  }
}

bool MatchRepetition(const SvaSequence& seq,
                     const std::vector<uint64_t>& vals) {
  uint32_t consecutive = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++consecutive;
    } else {
      break;
    }
  }
  return consecutive >= seq.rep_min && consecutive <= seq.rep_max;
}

bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals) {
  if (vals.empty()) return seq.rep_min == 0;
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }

  bool last_matches = seq.expr_check && seq.expr_check(vals.back());
  return last_matches && match_count >= seq.rep_min &&
         match_count <= seq.rep_max;
}

bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals) {
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }
  return match_count >= seq.rep_min && match_count <= seq.rep_max;
}

bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals) {
  if (vals.size() <= seq.delay_cycles) return false;
  uint64_t check_val = vals[seq.delay_cycles];
  return seq.expr_check && seq.expr_check(check_val);
}

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay) {
  EmptyConcatResult result;
  // (empty ##0 seq) and (seq ##0 empty): a length-0 endpoint can never align
  // with the neighboring sequence at the same time step, so neither matches.
  if (delay == 0) {
    result.matchable = false;
    return result;
  }
  // With delay n > 0 the empty operand contributes nothing, and the leftover
  // delay collapses onto the surviving operand as ##(n-1).
  result.matchable = true;
  result.effective_delay = delay - 1;
  // (seq ##n empty) is equivalent to (seq ##(n-1) `true), extending the match
  // one tick past seq; (empty ##n seq) is equivalent to (##(n-1) seq), which
  // merely prefixes the reduced delay.
  result.append_true = (side == EmptyConcatSide::kEmptyRight);
  return result;
}

bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match) {
  // A repetition that can take zero iterations is the disjunction of its empty
  // and nonempty cases; otherwise only the nonempty case is reachable.
  if (rep_min == 0) return empty_case_match || nonempty_case_match;
  return nonempty_case_match;
}

bool EvalSequenceAnd(bool a_match, bool b_match) { return a_match && b_match; }

SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time) {
  SequenceAndMatch result;
  result.matched = a_match && b_match;
  // The operands share a start time; the composite completes when the slower
  // operand does, i.e. at the later of the two end times.
  result.end_time = std::max(a_end_time, b_end_time);
  return result;
}

bool EvalSequenceOr(bool a_match, bool b_match) { return a_match || b_match; }

SequenceOrMatches EvalSequenceOrMatches(
    const std::vector<uint32_t>& a_end_times,
    const std::vector<uint32_t>& b_end_times) {
  SequenceOrMatches result;
  // The match set is the union of the two operands' matches: each operand match
  // carries through unchanged, keeping its own end time. Matches are not
  // merged, so both operands matching on the same tick yields two separate
  // entries.
  result.end_times = a_end_times;
  result.end_times.insert(result.end_times.end(), b_end_times.begin(),
                          b_end_times.end());
  result.matched = !result.end_times.empty();
  return result;
}

FirstMatchMatches EvalFirstMatch(
    const std::vector<uint32_t>& operand_end_times) {
  FirstMatchMatches result;
  // No match of the operand means no match of first_match.
  if (operand_end_times.empty()) return result;
  // The earliest ending clock tick among the operand's matches selects the
  // first match; every match ending later is discarded.
  uint32_t earliest =
      *std::min_element(operand_end_times.begin(), operand_end_times.end());
  // Ties at the earliest ending tick are all retained: when several operand
  // matches end on that tick, each one is a match of first_match.
  for (uint32_t end_time : operand_end_times) {
    if (end_time == earliest) result.end_times.push_back(end_time);
  }
  result.matched = true;
  return result;
}

bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len) {
  return a_match && b_match && a_len == b_len;
}

bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values) {
  return std::all_of(values.begin(), values.end(), check);
}

SequenceWithinMatch EvalSequenceWithin(bool inner_match, uint32_t inner_start,
                                       uint32_t inner_end, bool outer_match,
                                       uint32_t outer_start,
                                       uint32_t outer_end) {
  SequenceWithinMatch result;
  // seq1 within seq2 ≡ (1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect seq2: both
  // operands match and the match of seq1 falls inside the match of seq2. The
  // leading 1[*0:$] lets seq1 start no earlier than seq2's start, and the
  // trailing 1[*0:$] lets seq1 complete no later than seq2's completion.
  result.matched = inner_match && outer_match && inner_start >= outer_start &&
                   inner_end <= outer_end;
  // The intersection makes the composite cover seq2's whole interval, so it
  // completes at seq2's match point.
  result.end_time = outer_end;
  return result;
}

}  // namespace delta
