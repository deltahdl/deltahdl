#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "simulator/exec_task.h"

namespace delta {

struct Expr;
struct MailboxObject;
struct Stmt;
class Arena;
class SimContext;

// §15.4: the mailbox a call of the form `mbx.method(...)` names, or nullptr
// when the expression is not a method call whose receiver is a mailbox
// variable. `method` selects which call to answer for, so a caller that can
// only serve some of the methods asks about the ones it can serve.
MailboxObject* MailboxCallTarget(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view method);

// §15.4.1: the bound a mailbox new() names, its one argument, which defaults
// to 0, the unbounded mailbox.
int32_t MailboxBoundArg(const Expr* new_expr, SimContext& ctx, Arena& arena);

// §15.4.2, §15.4.4, §15.4.6 and §15.4.8: num(), try_put(), try_get() and
// try_peek() complete where they stand, so they are answered here as the
// values they return. put(), get() and peek() are not, because §15.4.3,
// §15.4.5 and §15.4.7 have them wait on the mailbox, and only a statement can
// suspend the process it belongs to.
bool TryEvalMailboxMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

// §15.4.1: `mbx = new(bound)` builds the mailbox with the bound it names.
// Returns true when the assignment was a mailbox construction.
bool TryMailboxNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §15.4.3, §15.4.5 and §15.4.7: whether a call statement is a put(), get() or
// peek() on a mailbox, the three methods that can suspend the process.
bool IsMailboxBlockingCall(const Expr* expr, SimContext& ctx, Arena& arena);

// §13.4 forbids a function to suspend the process that enables it, and
// §15.4.3, §15.4.5 and §15.4.7 have put(), get() and peek() suspend it only
// while a bounded mailbox is full or while the mailbox is empty. So a call
// of one of the three reached in a function body is served where it would
// not wait -- a put() on a mailbox with room places its message, a get() or
// peek() on one holding a message retrieves or copies it, through the same
// operations ExecMailboxCall's awaiters take -- and one that would wait is
// reported as an error under §13.4 at the call, with the mailbox and the
// variable as they were. Returns whether the call was one of the three.
// Reached through the expression evaluator, which answers num() and the
// try_* forms alone, a function's `mb.put(1)` placed nothing.
bool TryExecMailboxCallInFunction(const Expr* expr, SimContext& ctx,
                                  Arena& arena);

// §15.4.3, §15.4.5 and §15.4.7: runs a call IsMailboxBlockingCall answered
// true for, suspending the process while a bounded mailbox is full or while
// the mailbox is empty, and storing the message get() or peek() retrieved
// into the variable the call names.
ExecTask ExecMailboxCall(const Expr* expr, SimContext& ctx, Arena& arena);

}  // namespace delta
