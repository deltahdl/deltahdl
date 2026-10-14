#ifndef DELTA_ELABORATOR_COVERAGE_OPTION_RULES_H
#define DELTA_ELABORATOR_COVERAGE_OPTION_RULES_H

#include <string_view>

namespace delta {

class DiagEngine;
struct CovergroupContext;
struct CovergroupDecl;

// §19.10: whether `member` is a member of a covergroup's `option` structure,
// or of its `type_option` structure where `type_option` holds. A coverpoint's
// and a cross's structures hold some of the same members, which §19.7 and
// §19.7.1 tell apart by syntactic level.
bool IsCovergroupOptionMember(std::string_view member, bool type_option);

// The rules the coverage options the definition of `cg` sets obey, at the
// covergroup, coverpoint and cross levels, `ctx` answering for the names `cg`
// reads:
// - each names a member of the `option` or `type_option` structure (§19.10);
// - a constant weight is not negative (§19.7, §19.7.1);
// - a type option's value is a constant expression, its names constants and
//   its calls constant ones (§19.7.1); a covergroup formal there is the
//   parser's to report.
void CheckCoverageOptions(const CovergroupDecl& cg,
                          const CovergroupContext& ctx, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERAGE_OPTION_RULES_H
