#ifndef DELTA_SIMULATOR_SVA_ENGINE_SEQUENCES_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SEQUENCES_H_

#include <cstdint>
#include <functional>
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
  bool rep_max_is_dollar = false;
  std::function<bool(uint64_t)> expr_check;
};

bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

enum class EmptyConcatSide : uint8_t { kEmptyLeft, kEmptyRight };

struct EmptyConcatResult {
  bool matchable = false;
  uint32_t effective_delay = 0;
  bool append_true = false;
};

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay);

bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match);

bool EvalSequenceAnd(bool a_match, bool b_match);

struct SequenceAndMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time);

bool EvalSequenceOr(bool a_match, bool b_match);

struct SequenceOrMatches {
  bool matched = false;
  std::vector<uint32_t> end_times;
};
SequenceOrMatches EvalSequenceOrMatches(
    const std::vector<uint32_t>& a_end_times,
    const std::vector<uint32_t>& b_end_times);

struct FirstMatchMatches {
  bool matched = false;
  std::vector<uint32_t> end_times;
};
FirstMatchMatches EvalFirstMatch(
    const std::vector<uint32_t>& operand_end_times);

bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);

struct IntersectOperandMatch {
  uint32_t length = 0;
  uint32_t match_point = 0;
};

std::vector<IntersectOperandMatch> EvalSequenceIntersectMatches(
    const std::vector<IntersectOperandMatch>& a_matches,
    const std::vector<IntersectOperandMatch>& b_matches);

bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

struct SequenceWithinMatch {
  bool matched = false;
  uint32_t end_time = 0;
};

struct SequenceMatchSpan {
  bool matched = false;
  uint32_t start_time = 0;
  uint32_t end_time = 0;
};

SequenceWithinMatch EvalSequenceWithin(const SequenceMatchSpan& inner,
                                       const SequenceMatchSpan& outer);

}  // namespace delta

#endif
