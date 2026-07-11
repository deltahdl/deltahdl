#pragma once

#include <cstdint>

namespace delta {

// §16.12.22 classifies a sequence by what kinds of matches it admits. The
// formal definition is in §F.4.3 (admits_empty) and §F.5; this enum lets the
// elaborator carry the classification around at AST level.
enum class SequenceMatchClass : uint8_t {
  // §16.12.22: degenerate — admits no match at all (e.g. 1'b1 intersect (1'b1
  // ##1 1'b1)).
  kAdmitsNoMatch,
  // §16.12.22: degenerate — admits only empty matches (e.g. 1'b1[*0]).
  kAdmitsOnlyEmpty,
  // §16.12.22: admits at least one nonempty match and no empty match. This is
  // the pure nondegenerate case (e.g. a ##1 b).
  kAdmitsAtLeastOneNonempty,
  // §16.12.22: admits both empty and nonempty matches (e.g. a[*0:2], which the
  // clause cites explicitly). Still nondegenerate — it admits a nonempty match
  // — yet it also admits an empty match, so restriction (a) must reject it as a
  // property while restrictions (b) and (c) still accept it as an antecedent.
  kAdmitsBothEmptyAndNonempty,
};

// §16.12.22: degenerate sequences either admit no match or admit only empty
// matches. The remaining class is nondegenerate.
bool IsDegenerate(SequenceMatchClass m);
bool IsNondegenerate(SequenceMatchClass m);
bool AdmitsAnyEmptyMatch(SequenceMatchClass m);

// §16.12.22 lists three contexts in which sequences are restricted. We model
// the context so the elaborator can route a sequence through the correct
// check.
enum class SequenceUsageContext : uint8_t {
  // §16.12.22(a): used as a property.
  kAsProperty,
  // §16.12.22(b): antecedent of overlapping implication |->.
  kOverlappingImplicationAntecedent,
  // §16.12.22(c): antecedent of nonoverlapping implication |=>.
  kNonoverlappingImplicationAntecedent,
};

// §16.12.22 enumerates the restriction for each context.
//   (a) used as a property: shall be nondegenerate and not admit any empty
//       match. Disallows kAdmitsOnlyEmpty even though kAdmitsOnlyEmpty would
//       otherwise be admissible under (c).
//   (b) antecedent of |->: shall be nondegenerate.
//   (c) antecedent of |=>: shall admit at least one match (so kAdmitsNoMatch
//       is illegal). kAdmitsOnlyEmpty is explicitly allowed here.
bool IsSequenceUsageLegal(SequenceUsageContext ctx, SequenceMatchClass m);

}  // namespace delta
