#include "elaborator/sequence_degeneracy.h"

namespace delta {

bool IsDegenerate(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsNoMatch ||
         m == SequenceMatchClass::kAdmitsOnlyEmpty;
}

bool IsNondegenerate(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsAtLeastOneNonempty;
}

bool AdmitsAnyEmptyMatch(SequenceMatchClass m) {
  // §16.12.22: kAdmitsOnlyEmpty trivially admits empty; the nondegenerate
  // class may or may not admit empty, so we treat that combined case
  // separately in callers when the distinction matters. This helper answers
  // "admits an empty match in addition to whatever else" only for the
  // unambiguous class.
  return m == SequenceMatchClass::kAdmitsOnlyEmpty;
}

bool IsSequenceUsageLegal(SequenceUsageContext ctx, SequenceMatchClass m) {
  switch (ctx) {
    case SequenceUsageContext::kAsProperty:
      // §16.12.22(a): must be nondegenerate AND not admit any empty match.
      // A nondegenerate sequence that happens to admit an empty match in
      // addition to nonempty ones is therefore illegal here.
    case SequenceUsageContext::kOverlappingImplicationAntecedent:
      // §16.12.22(b): nondegenerate.
      return IsNondegenerate(m);
    case SequenceUsageContext::kNonoverlappingImplicationAntecedent:
      // §16.12.22(c): must admit at least one match. kAdmitsOnlyEmpty is
      // explicitly allowed.
      return m != SequenceMatchClass::kAdmitsNoMatch;
  }
  return false;
}

}  // namespace delta
