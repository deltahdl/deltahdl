#pragma once

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

bool TryArrayPatternEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

bool TryDynamicStructEquality(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

}  // namespace delta
