#ifndef DELTA_ELABORATOR_CROSS_BIN_RULES_H
#define DELTA_ELABORATOR_CROSS_BIN_RULES_H

namespace delta {

class DiagEngine;
struct CoverCrossDecl;
struct CovergroupContext;
struct CovergroupDecl;

void CheckCrossBinRules(const CoverCrossDecl& cross, const CovergroupDecl& cg,
                        const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif
