#pragma once

#include <functional>

namespace delta {

class SimContext;
struct Expr;

// §21.2.3 (printed page 665) with §8.5, §8.6 and §8.9: a monitored list is
// written again at the end of any time step in which one of its arguments
// changed, and a class property is such an argument -- `h.p` through a handle,
// the bare `p` or `this.p` of the method's object, a static property `C::s`.
// A property is a slot of an object or of its class rather than a Variable,
// so no variable watcher sees it written. For each property `expr` reads this
// arms a watcher on the object, or on the class for a static one, that
// compares the property with the value it last saw and calls `changed` when it
// differs; `changed` answers true once the monitor it serves is gone, which
// retires the watcher. Called where the monitor is called, so the method's
// object is the one in scope.
void WatchClassMembersRead(const Expr* expr, SimContext& ctx,
                           const std::function<bool()>& changed);

}  // namespace delta
