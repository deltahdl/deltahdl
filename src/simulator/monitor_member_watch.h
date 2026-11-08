#pragma once

#include <functional>

namespace delta {

class SimContext;
struct Expr;

void WatchClassMembersRead(const Expr* expr, SimContext& ctx,
                           const std::function<bool()>& changed);

}  // namespace delta
