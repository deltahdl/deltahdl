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
  // §16.9.2: exact count and dollar-max are always well-formed. A finite
  // range requires min ≤ max.
  if (c.is_exact_count) return true;
  if (c.max_is_dollar) return true;
  return c.min <= c.max;
}

RepetitionCount NormalizeStarShortcut() {
  // §16.9.2: [*] ≡ [*0:$].
  return MakeDollarRange(0);
}

RepetitionCount NormalizePlusShortcut() {
  // §16.9.2: [+] ≡ [*1:$].
  return MakeDollarRange(1);
}

bool IsRepetitionAllowedOn(RepetitionKind kind, bool operand_is_boolean_expr,
                           bool boolean_has_attached_match_item) {
  switch (kind) {
    case RepetitionKind::kConsecutive:
      // §16.9.2: consecutive repetition applies to any sequence_expr,
      // Boolean or not, with or without an attached match item.
      return true;
    case RepetitionKind::kGoto:
    case RepetitionKind::kNonconsecutive:
      // §16.9.2: goto and nonconsecutive repetition operators apply only to
      // Boolean expressions; and they cannot be applied to a Boolean to
      // which a sequence_match_item has been attached.
      if (!operand_is_boolean_expr) return false;
      return !boolean_has_attached_match_item;
  }
  return false;
}

bool IsZeroRepetitionPermitted(RepetitionKind kind) {
  // §16.9.2: only the consecutive form has a defined zero-iteration case;
  // goto/nonconsecutive require a successful match of the Boolean operand
  // and a zero iteration count would leave no match for the operator's
  // semantics to anchor on.
  return kind == RepetitionKind::kConsecutive;
}

}  // namespace delta
