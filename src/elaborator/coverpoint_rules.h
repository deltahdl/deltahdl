#ifndef DELTA_ELABORATOR_COVERPOINT_RULES_H
#define DELTA_ELABORATOR_COVERPOINT_RULES_H

namespace delta {

class DiagEngine;
struct CoverPointDecl;
struct CovergroupContext;
struct CovergroupDecl;

// The rules a coverpoint `cp` of the covergroup `cg` obeys whatever the type of
// its expression, `ctx` answering for the names `cg` reads:
// - a data type written before its label is integral or real (§19.5);
// - its expression gives an integral or real value (§19.5);
// - no ignore_bins takes `default` or `default sequence` as its value (§19.5,
//   §19.5.5);
// - the size of a fixed number of bins, where it is constant, is positive
//   (§19.5.1);
// - a bin naming a coverpoint before `with` names its own, and a bin's `with`
//   expression gives a value assignment compatible with an integral type
//   (§19.5.1.1).
void CheckCoverpointRules(const CoverPointDecl& cp, const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERPOINT_RULES_H
