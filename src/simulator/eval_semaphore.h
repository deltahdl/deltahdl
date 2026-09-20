#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct SemaphoreObject;
struct Stmt;
class Arena;
class SimContext;

// §15.3: the semaphore a call of the form `sem.method(...)` names, or nullptr
// when the expression is not a method call whose receiver is a semaphore
// variable. `method` selects which call to answer for, so a caller that can
// only serve some of the methods asks about the ones it can serve.
SemaphoreObject* SemaphoreCallTarget(const Expr* expr, SimContext& ctx,
                                     std::string_view method);

// §15.3: the number of keys a semaphore method call asks for. Each of the
// methods takes the count as its one argument and defaults it, so a call
// written without arguments asks for `absent`.
int32_t SemaphoreKeyArg(const Expr* expr, SimContext& ctx, Arena& arena,
                        int32_t absent);

// §15.3.2 and §15.3.4: put() returns keys to the bucket and try_get() procures
// them without waiting, so both complete where they stand and are answered
// here. get() is not, because §15.3 has it wait until enough keys are in the
// bucket, and only a statement can suspend the process it belongs to.
bool TryEvalSemaphoreMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

// §13.4 forbids a function to suspend the process that enables it, and
// §15.3.3 has get() suspend it only while the bucket holds fewer keys than
// the call asks for. So a get() reached in a function body is served where
// it would not wait -- the keys are taken from the bucket as
// SemaphoreGetAwaiter takes them before it would park the process -- and one
// that would wait is reported as an error under §13.4 at the call, with the
// bucket as it was. Returns whether the call was a semaphore's get(). put()
// and try_get() complete where they stand and are answered by the expression
// evaluator (TryEvalSemaphoreMethodCall) in a function as anywhere else.
// Reached through the expression evaluator alone, a function's `s.get(1)`
// took nothing.
bool TryExecSemaphoreCallInFunction(const Expr* expr, SimContext& ctx,
                                    Arena& arena);

// §15.3.1 and §15.4.1 with §26.3: the key the target of `target = new(...)`
// is held under -- an identifier's own text, or the "p.name" a package's
// variable named through the package scope resolution operator, `p::name`,
// is created under (CreatePackageDataVariables in lowerer_register.cpp),
// given the arena's lifetime. Empty for any other target shape. Shared with
// TryMailboxNewAssign, so a semaphore and a mailbox resolve a scoped target
// alike.
std::string_view ScopedOrBareTargetKey(const Expr* lhs, Arena& arena);

// §15.3.1: `sem = new(keyCount)` fills the bucket with the keys it names.
// Returns true when the assignment was a semaphore construction.
bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
