#ifndef DELTA_ELABORATOR_COVERAGE_OPTION_RULES_H
#define DELTA_ELABORATOR_COVERAGE_OPTION_RULES_H

#include <string_view>

namespace delta {

class DiagEngine;
struct CovergroupContext;
struct CovergroupDecl;

bool IsCovergroupOptionMember(std::string_view member, bool type_option);

void CheckCoverageOptions(const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif
