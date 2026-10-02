#pragma once

#include <string_view>
#include <vector>

namespace delta {

class DiagEngine;
struct CovergroupDecl;
struct Expr;

// The first identifier anywhere in `e` that is one of `names`, or null.
const Expr* FindNamedIdentifier(const Expr* e,
                                const std::vector<std::string_view>& names);

// §19.8.1: a formal argument of an overridden sample method may designate only
// a coverpoint or a conditional guard expression. Reports each formal `cg`
// names in a coverage-option value, a bin specification or a cross bin's
// select expression, its coverpoint expressions, cross items and `iff` guards
// being the contexts left legal.
void ReportSampleFormalsOutsideCoverpoints(const CovergroupDecl& cg,
                                           DiagEngine& diag);

}  // namespace delta
