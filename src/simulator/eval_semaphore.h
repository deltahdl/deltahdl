#pragma once

#include <cstdint>

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

// §15.3.1: `sem = new(keyCount)` fills the bucket with the keys it names.
// Returns true when the assignment was a semaphore construction.
bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
