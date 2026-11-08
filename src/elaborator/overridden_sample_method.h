#pragma once

#include <cstdint>

namespace delta {

enum class CovergroupNameContext : uint8_t {
  kCoverpointExpression,
  kConditionalGuardExpression,
  kCoverageOptionAssignment,
  kCrossList,
  kBinsExpression,
  kOther,
};

bool SampleFormalUsageIsLegal(CovergroupNameContext context);

enum class CovergroupNameResolution : uint8_t {
  kSampleFormal,
  kEnclosingScope,
  kUnresolved,
};

CovergroupNameResolution ResolveCovergroupName(bool name_is_sample_formal,
                                               bool name_in_enclosing_scope);

}  // namespace delta
