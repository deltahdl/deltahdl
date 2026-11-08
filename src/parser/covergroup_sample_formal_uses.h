#pragma once

#include <string_view>
#include <vector>

namespace delta {

class DiagEngine;
struct CovergroupDecl;
struct Expr;

const Expr* FindNamedIdentifier(const Expr* e,
                                const std::vector<std::string_view>& names);

void ReportSampleFormalsOutsideCoverpoints(const CovergroupDecl& cg,
                                           DiagEngine& diag);

}  // namespace delta
