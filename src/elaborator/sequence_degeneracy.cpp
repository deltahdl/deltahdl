#include "elaborator/sequence_degeneracy.h"

namespace delta {

bool IsDegenerate(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsNoMatch ||
         m == SequenceMatchClass::kAdmitsOnlyEmpty;
}

bool IsNondegenerate(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsAtLeastOneNonempty ||
         m == SequenceMatchClass::kAdmitsBothEmptyAndNonempty;
}

bool AdmitsAnyEmptyMatch(SequenceMatchClass m) {
  return m == SequenceMatchClass::kAdmitsOnlyEmpty ||
         m == SequenceMatchClass::kAdmitsBothEmptyAndNonempty;
}

bool IsSequenceUsageLegal(SequenceUsageContext ctx, SequenceMatchClass m) {
  switch (ctx) {
    case SequenceUsageContext::kAsProperty:
      return IsNondegenerate(m) && !AdmitsAnyEmptyMatch(m);
    case SequenceUsageContext::kOverlappingImplicationAntecedent:
      return IsNondegenerate(m);
    case SequenceUsageContext::kNonoverlappingImplicationAntecedent:
      return m != SequenceMatchClass::kAdmitsNoMatch;
  }
  return false;
}

}  // namespace delta
