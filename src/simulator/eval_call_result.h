#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// §8.6 with §8.20: a method call whose return type is a class yields a handle,
// and a member selected on the call, `n.self().v` or `n.mk(1).mk(2).v`, or a
// method called on it, `c.some_method(7).who()`, applies to the object the call
// returned. That object is denoted by no name -- it exists once the call has
// run -- so the paths that resolve a member access or a method call by the
// variable on its handle side (TryClassPropertyAccess in eval_expr.cpp and
// TryEvalClassMethodCall in eval_function.cpp) answer for neither; each of the
// two below evaluates the handle side instead and reads or dispatches on the
// object it refers to.

// The property `expr->rhs` of the object the handle side of the member access
// `expr` evaluates to, where that side is a method call or a member path that
// starts at one. False for any other side, and for a call that returned the
// null handle, which the remaining member-access paths answer as they did.
bool TryEvalCallResultMember(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// The method call `expr`, `<call>.m(...)` or `<call>.p.m(...)`, run on the
// object its handle side evaluates to. §8.20 dispatches a virtual method by
// the object's own type, which is the type the handle is read with here: the
// return type the call declares is a base of it at most (§8.20's covariant
// return), and a non-virtual method it shadows is not told apart. False for a
// handle side that starts at no call, for a null result and for a method the
// object's class does not have.
bool TryEvalCallResultMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta
