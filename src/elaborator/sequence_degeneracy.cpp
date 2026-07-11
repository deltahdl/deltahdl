#include "elaborator/sequence_degeneracy.h"

namespace delta {

bool IsDegenerate(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsNoMatch ||
         m == SequenceMatchClass::kAdmitsOnlyEmpty;
}

bool IsNondegenerate(SequenceMatchClass m) {
  // §16.12.22: nondegenerate means admitting at least one nonempty match. Both
  // the pure-nonempty class and the mixed empty+nonempty class qualify.
  return m == SequenceMatchClass::kAdmitsAtLeastOneNonempty ||
         m == SequenceMatchClass::kAdmitsBothEmptyAndNonempty;
}

bool AdmitsAnyEmptyMatch(SequenceMatchClass m) {
  // §16.12.22: a sequence admits an empty match when it admits only empty
  // matches or when it admits empty matches alongside nonempty ones (e.g.
  // a[*0:2]). The pure-nonempty class is the only one that admits no empty
  // match.
  return m == SequenceMatchClass::kAdmitsOnlyEmpty ||
         m == SequenceMatchClass::kAdmitsBothEmptyAndNonempty;
}

bool IsSequenceUsageLegal(SequenceUsageContext ctx, SequenceMatchClass m) {
  switch (ctx) {
    case SequenceUsageContext::kAsProperty:
      // §16.12.22(a): must be nondegenerate AND not admit any empty match. A
      // nondegenerate sequence that also admits an empty match (the mixed
      // class, e.g. a[*0:2]) is therefore illegal here even though it is legal
      // as an implication antecedent.
      return IsNondegenerate(m) && !AdmitsAnyEmptyMatch(m);
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
