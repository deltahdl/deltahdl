#pragma once

#include <cstdint>

namespace delta {

enum class RepetitionKind : uint8_t {
  kConsecutive,
  kGoto,
  kNonconsecutive,
};

struct RepetitionCount {
  unsigned long long min = 0;
  unsigned long long max = 0;
  bool max_is_dollar = false;
  bool is_exact_count = false;
};

RepetitionCount MakeExactCount(unsigned long long n);
RepetitionCount MakeFiniteRange(unsigned long long lo, unsigned long long hi);
RepetitionCount MakeDollarRange(unsigned long long lo);

bool IsRepetitionCountWellFormed(const RepetitionCount& c);

RepetitionCount NormalizeStarShortcut();
RepetitionCount NormalizePlusShortcut();

bool IsRepetitionAllowedOn(RepetitionKind kind, bool operand_is_boolean_expr,
                           bool boolean_has_attached_match_item);

bool IsZeroRepetitionPermitted(RepetitionKind kind);

}  // namespace delta
