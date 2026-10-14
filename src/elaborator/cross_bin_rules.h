#ifndef DELTA_ELABORATOR_CROSS_BIN_RULES_H
#define DELTA_ELABORATOR_CROSS_BIN_RULES_H

namespace delta {

class DiagEngine;
struct CoverCrossDecl;
struct CovergroupContext;
struct CovergroupDecl;

// The rules the bins of the cross `cross` of the covergroup `cg` obey, `ctx`
// answering for the names `cg` reads:
// - a constant `matches` count is a positive integer (§19.6.1.2, §19.6.1.4);
// - a cross_identifier selecting bin tuples names the enclosing cross alone
//   (§19.6.1.2);
// - a cross_set_expression naming an array names one whose elements can be
//   the cross's CrossValType, so no array of integral, real or string
//   elements (§19.6.1.4).
void CheckCrossBinRules(const CoverCrossDecl& cross, const CovergroupDecl& cg,
                        const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CROSS_BIN_RULES_H
