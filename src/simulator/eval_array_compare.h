#pragma once

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

// §11.4.5 with §7.6 and §10.9: `expr`, an equality `==` or `!=` between an
// unpacked array -- a variable, a subroutine formal, a queue, or an array
// property of an object -- and an assignment pattern, typed or untyped,
// positional or replicated, compared element by element into `out`. False,
// with `out` left alone, where `expr` is no such comparison.
bool TryArrayPatternEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// §11.2.2 with §7.5: `expr`, an equality `==`, `!=`, `===` or `!==` between
// two unpacked structures holding a dynamic array member -- variables, class
// properties or members -- compared member by member into `out`, the dynamic
// member by the elements it holds rather than the handle naming them. False,
// with `out` left alone, where `expr` is no such comparison or, for `==` and
// `!=`, a member compared holds an unknown bit, which the comparison of the
// values themselves answers.
bool TryDynamicStructEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

}  // namespace delta
