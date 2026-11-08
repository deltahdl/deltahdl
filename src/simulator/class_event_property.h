#pragma once

#include <string_view>

namespace delta {

struct Expr;
struct Logic4Vec;
struct Variable;
class SimContext;
class Arena;

Variable* ClassEventVariable(const Expr* expr, SimContext& ctx, Arena& arena);

Variable* EventArrayElement(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EventIdentityOf(const Expr* expr, SimContext& ctx, Arena& arena);

Variable* TriggerTargetEvent(const Expr* expr, std::string_view name,
                             SimContext& ctx);

bool TryClassEventTriggered(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

}  // namespace delta
