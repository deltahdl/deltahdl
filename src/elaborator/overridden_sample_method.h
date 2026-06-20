#pragma once

#include <cstdint>

namespace delta {

// §19.8.1: a covergroup may override its built-in sample() method with a
// triggering function that accepts formal arguments. The rules below constrain
// how those sample formal arguments may be referenced and resolved within the
// covergroup.

// §19.8.1: the syntactic contexts in which a name may appear inside a
// covergroup body. A formal argument of an overridden sample method is
// restricted to only a subset of these.
enum class CovergroupNameContext : uint8_t {
  kCoverpointExpression,        // the expression sampled by a coverpoint
  kConditionalGuardExpression,  // an "iff" conditional guard expression
  kCoverageOptionAssignment,    // an option.* / type_option.* assignment
  kCrossList,                   // the coverpoint list of a cross
  kBinsExpression,              // a bins value/transition expression
  kOther,
};

// §19.8.1: a formal argument of an overridden sample method may only designate
// a coverpoint or a conditional guard expression. It is an error to use a
// sample formal argument in any other context.
bool SampleFormalUsageIsLegal(CovergroupNameContext context);

// §19.8.1: how a name referenced inside a covergroup resolves once the sample
// method has been overridden with formal arguments.
enum class CovergroupNameResolution : uint8_t {
  kSampleFormal,    // bound to a formal of the overridden sample method
  kEnclosingScope,  // bound to a declaration in the enclosing scope
  kUnresolved,      // not visible in either place
};

// §19.8.1: the formal arguments of an overridden sample method are searched
// before the enclosing scope, so a name that matches a sample formal resolves
// to that formal even when the enclosing scope also declares it.
CovergroupNameResolution ResolveCovergroupName(bool name_is_sample_formal,
                                               bool name_in_enclosing_scope);

}  // namespace delta
