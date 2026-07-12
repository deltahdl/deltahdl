#include "elaborator/overridden_sample_method.h"

namespace delta {

bool SampleFormalUsageIsLegal(CovergroupNameContext context) {
  // §19.8.1: only a coverpoint or a conditional guard expression may designate
  // a sample formal argument; every other context is an error.
  switch (context) {
    case CovergroupNameContext::kCoverpointExpression:
    case CovergroupNameContext::kConditionalGuardExpression:
    // A cross's item list names coverpoints (a bare variable there implicitly
    // creates one), so a sample formal used as a cross item still designates a
    // coverpoint and is legal -- exactly the `cross x, a` in §19.8.1's own
    // valid example, where a and x are the overridden sample method's formals.
    case CovergroupNameContext::kCrossList:
      return true;
    case CovergroupNameContext::kCoverageOptionAssignment:
    case CovergroupNameContext::kBinsExpression:
    case CovergroupNameContext::kOther:
      return false;
  }
  return false;
}

CovergroupNameResolution ResolveCovergroupName(bool name_is_sample_formal,
                                               bool name_in_enclosing_scope) {
  // §19.8.1: the sample formals are searched before the enclosing scope, so a
  // match among them wins even if the enclosing scope declares the same name.
  if (name_is_sample_formal) return CovergroupNameResolution::kSampleFormal;
  if (name_in_enclosing_scope) return CovergroupNameResolution::kEnclosingScope;
  return CovergroupNameResolution::kUnresolved;
}

}  // namespace delta
