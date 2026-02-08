#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena);

}  // namespace delta
