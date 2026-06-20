#pragma once

#include <cstdint>

namespace delta {

// §16.9.2 BNF: the three kinds of repetition each get their own bracketed
// operator. Consecutive applies to any sequence_expr; goto and nonconsecutive
// apply only to Boolean expressions.
enum class RepetitionKind : uint8_t {
  kConsecutive,
  kGoto,
  kNonconsecutive,
};

// §16.9.2: the number of iterations is given either by exact count (a single
// non-negative integer constant expression) or as a range. The maximum may
// be the dollar sign ($) — a finite but unbounded upper bound. The range
// form has the constraint min ≤ max when max is a finite constant.
struct RepetitionCount {
  unsigned long long min = 0;
  unsigned long long max = 0;
  bool max_is_dollar = false;
  bool is_exact_count = false;
};

RepetitionCount MakeExactCount(unsigned long long n);
RepetitionCount MakeFiniteRange(unsigned long long lo, unsigned long long hi);
RepetitionCount MakeDollarRange(unsigned long long lo);

// §16.9.2: if both min and max are defined by non-negative integer constant
// expressions, min ≤ max. Exact-count and dollar-max are trivially
// well-formed.
bool IsRepetitionCountWellFormed(const RepetitionCount& c);

// §16.9.2: the [*] shortcut is equivalent to [*0:$]; [+] is equivalent to
// [*1:$]. Both are consecutive repetition operators with the noted defaults.
RepetitionCount NormalizeStarShortcut();
RepetitionCount NormalizePlusShortcut();

// §16.9.2: goto and nonconsecutive repetition can be applied only to Boolean
// expressions. In particular, neither may be applied to a Boolean expression
// to which a sequence_match_item (see §16.10, §16.11) has been attached.
bool IsRepetitionAllowedOn(RepetitionKind kind, bool operand_is_boolean_expr,
                           bool boolean_has_attached_match_item);

// §16.9.2.1 (descendant; here only as the reading anchor): a zero repetition
// number produces an empty sequence. The admits_empty rules in §F.4.3 then
// route the empty-match handling. The flag here is the elaborator's hook
// into the boundary case.
bool IsZeroRepetitionPermitted(RepetitionKind kind);

}  // namespace delta
