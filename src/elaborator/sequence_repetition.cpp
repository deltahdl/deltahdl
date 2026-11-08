#include "elaborator/sequence_repetition.h"

namespace delta {

RepetitionCount MakeExactCount(unsigned long long n) {
  RepetitionCount c;
  c.min = n;
  c.max = n;
  c.is_exact_count = true;
  return c;
}

RepetitionCount MakeFiniteRange(unsigned long long lo, unsigned long long hi) {
  RepetitionCount c;
  c.min = lo;
  c.max = hi;
  return c;
}

RepetitionCount MakeDollarRange(unsigned long long lo) {
  RepetitionCount c;
  c.min = lo;
  c.max_is_dollar = true;
  return c;
}

bool IsRepetitionCountWellFormed(const RepetitionCount& c) {
  if (c.is_exact_count) return true;
  if (c.max_is_dollar) return true;
  return c.min <= c.max;
}

RepetitionCount NormalizeStarShortcut() { return MakeDollarRange(0); }

RepetitionCount NormalizePlusShortcut() { return MakeDollarRange(1); }

bool IsRepetitionAllowedOn(RepetitionKind kind, bool operand_is_boolean_expr,
                           bool boolean_has_attached_match_item) {
  switch (kind) {
    case RepetitionKind::kConsecutive:
      return true;
    case RepetitionKind::kGoto:
    case RepetitionKind::kNonconsecutive:
      if (!operand_is_boolean_expr) return false;
      return !boolean_has_attached_match_item;
  }
  return false;
}

bool IsZeroRepetitionPermitted(RepetitionKind kind) {
  return kind == RepetitionKind::kConsecutive;
}

}  // namespace delta
