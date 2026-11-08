#include "elaborator/overridden_sample_method.h"

namespace delta {

bool SampleFormalUsageIsLegal(CovergroupNameContext context) {
  switch (context) {
    case CovergroupNameContext::kCoverpointExpression:
    case CovergroupNameContext::kConditionalGuardExpression:
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
  if (name_is_sample_formal) return CovergroupNameResolution::kSampleFormal;
  if (name_in_enclosing_scope) return CovergroupNameResolution::kEnclosingScope;
  return CovergroupNameResolution::kUnresolved;
}

}  // namespace delta
