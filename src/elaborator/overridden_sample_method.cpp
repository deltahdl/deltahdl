#include "elaborator/overridden_sample_method.h"

namespace delta {

bool SampleFormalUsageIsLegal(CovergroupNameContext context) {
  // §19.8.1: only a coverpoint or a conditional guard expression may designate
  // a sample formal argument; every other context is an error.
  switch (context) {
    case CovergroupNameContext::kCoverpointExpression:
    case CovergroupNameContext::kConditionalGuardExpression:
      return true;
    case CovergroupNameContext::kCoverageOptionAssignment:
    case CovergroupNameContext::kCrossList:
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
