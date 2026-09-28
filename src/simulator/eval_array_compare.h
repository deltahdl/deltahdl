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

}  // namespace delta
