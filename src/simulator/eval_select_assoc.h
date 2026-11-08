#pragma once

namespace delta {

struct Expr;
struct Logic4Vec;
class SimContext;
class Arena;

bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                    Logic4Vec& out);

}  // namespace delta
