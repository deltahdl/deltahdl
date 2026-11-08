#pragma once

#include <cstdint>

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct Logic4Vec;
struct NbaSample;
struct Stmt;

bool TryModportExpressionRead(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

bool TryModportExpressionWrite(const Expr* lhs, const Logic4Vec& value,
                               SimContext& ctx, Arena& arena);

bool TryModportExpressionAssign(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

bool TryModportExpressionNonblocking(const Stmt* stmt, const NbaSample& sample,
                                     uint64_t delay_ticks, SimContext& ctx,
                                     Arena& arena);

}  // namespace delta
