#ifndef DELTA_ELABORATOR_COVERPOINT_RULES_H
#define DELTA_ELABORATOR_COVERPOINT_RULES_H

namespace delta {

class DiagEngine;
struct CoverPointDecl;
struct CovergroupContext;
struct CovergroupDecl;

void CheckCoverpointRules(const CoverPointDecl& cp, const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif
