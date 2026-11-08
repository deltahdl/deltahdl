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
  return consecutive >= seq.rep_min &&
         (seq.rep_max_is_dollar || consecutive <= seq.rep_max);
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
         (seq.rep_max_is_dollar || match_count <= seq.rep_max);
}

bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals) {
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }
  return match_count >= seq.rep_min &&
         (seq.rep_max_is_dollar || match_count <= seq.rep_max);
}

bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals) {
  if (vals.size() <= seq.delay_cycles) return false;
  uint64_t check_val = vals[seq.delay_cycles];
  return seq.expr_check && seq.expr_check(check_val);
}

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay) {
  EmptyConcatResult result;
  if (delay == 0) {
    result.matchable = false;
    return result;
  }
  result.matchable = true;
  result.effective_delay = delay - 1;
  result.append_true = (side == EmptyConcatSide::kEmptyRight);
  return result;
}

bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match) {
  if (rep_min == 0) return empty_case_match || nonempty_case_match;
  return nonempty_case_match;
}

bool EvalSequenceAnd(bool a_match, bool b_match) { return a_match && b_match; }

SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time) {
  SequenceAndMatch result;
  result.matched = a_match && b_match;
  result.end_time = std::max(a_end_time, b_end_time);
  return result;
}

bool EvalSequenceOr(bool a_match, bool b_match) { return a_match || b_match; }

SequenceOrMatches EvalSequenceOrMatches(
    const std::vector<uint32_t>& a_end_times,
    const std::vector<uint32_t>& b_end_times) {
  SequenceOrMatches result;
  result.end_times = a_end_times;
  result.end_times.insert(result.end_times.end(), b_end_times.begin(),
                          b_end_times.end());
  result.matched = !result.end_times.empty();
  return result;
}

FirstMatchMatches EvalFirstMatch(
    const std::vector<uint32_t>& operand_end_times) {
  FirstMatchMatches result;
  if (operand_end_times.empty()) return result;
  uint32_t earliest =
      *std::min_element(operand_end_times.begin(), operand_end_times.end());
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

std::vector<IntersectOperandMatch> EvalSequenceIntersectMatches(
    const std::vector<IntersectOperandMatch>& a_matches,
    const std::vector<IntersectOperandMatch>& b_matches) {
  std::vector<IntersectOperandMatch> result;
  for (const auto& a : a_matches) {
    for (const auto& b : b_matches) {
      if (a.length == b.length) {
        result.push_back({a.length, a.match_point});
      }
    }
  }
  return result;
}

bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values) {
  return std::all_of(values.begin(), values.end(), check);
}

SequenceWithinMatch EvalSequenceWithin(const SequenceMatchSpan& inner,
                                       const SequenceMatchSpan& outer) {
  SequenceWithinMatch result;
  result.matched = inner.matched && outer.matched &&
                   inner.start_time >= outer.start_time &&
                   inner.end_time <= outer.end_time;
  result.end_time = outer.end_time;
  return result;
}

}  // namespace delta
