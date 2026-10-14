#ifndef DELTA_ELABORATOR_COVERGROUP_EXPRESSION_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_EXPRESSION_RULES_H

#include <string_view>

namespace delta {

class DiagEngine;
struct CovergroupContext;
struct CovergroupDecl;
struct ModuleItem;

// §19.5: what the covergroup_expressions of `cg` may read and call, `ctx`
// answering for the names `cg` reads where it is declared. They are, of a
// coverpoint's bins, every value, bound and tolerance of a range list, of a
// transition and of its repetition, the size of a fixed number of bins and the
// `with` expression; and of a cross's bins (§19.6) every value of an
// `intersect` range list, the `with` expression and the `matches` count. A
// set_covergroup_expression follows §19.5.1.2 and a cross_set_expression
// §19.6.1.4 instead.
// - A name is read as a variable only where it is a constant, a global or
//   instance constant (§8.19), or a formal of `cg` that is not `ref`; the
//   candidate `item` of a coverpoint bin's `with` expression and the items of
//   a cross in its bins' `with` expressions are the values being selected.
// - A function called takes no output, inout or non-const ref argument, is
//   automatic or keeps no state, has no side effect, and reads no variable
//   outside it that is no constant; a system function called is a constant
//   system function (§11.2.1).
void CheckCovergroupExpressions(const CovergroupDecl& cg,
                                const CovergroupContext& ctx, DiagEngine& diag);

// A variable outside the function `fn` that is no constant, `ctx` answering
// which names are, and that `fn` reads; empty where it reads none (§19.5,
// §13.4.3).
std::string_view NonConstantReadOutside(const ModuleItem& fn,
                                        const CovergroupContext& ctx);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_EXPRESSION_RULES_H
