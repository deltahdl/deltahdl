#ifndef DELTA_ELABORATOR_COVERGROUP_EXPRESSION_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_EXPRESSION_RULES_H

#include <string_view>

namespace delta {

class DiagEngine;
struct CovergroupContext;
struct CovergroupDecl;
struct ModuleItem;

void CheckCovergroupExpressions(const CovergroupDecl& cg,
                                const CovergroupContext& ctx, DiagEngine& diag);

std::string_view NonConstantReadOutside(const ModuleItem& fn,
                                        const CovergroupContext& ctx);

}  // namespace delta

#endif
