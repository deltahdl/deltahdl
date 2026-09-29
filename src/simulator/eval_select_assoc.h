#pragma once

namespace delta {

struct Expr;
struct Logic4Vec;
class SimContext;
class Arena;

// §7.8: reads into `out` the entry of an associative array that `expr`, a
// select of one element, designates, and says whether `expr` designates one.
// A missing entry, or an integral index holding an x or z bit, reads the
// array's default and, with no user default configured, warns (§7.8.6).
bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                    Logic4Vec& out);

}  // namespace delta
