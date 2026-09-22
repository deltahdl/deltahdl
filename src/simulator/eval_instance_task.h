#pragma once

#include "common/types.h"
#include "simulator/eval_function_internal.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

// §13.3 with §8.6: a task enabled through an object handle, `h.t(args)`.
// Resolves the handle and the task, and when `expr` is such a call to an
// instance task, pushes the frame its body runs in -- the defining class as
// the enclosing scope (§8.15), a scope, `this`, the queue and associative
// reference frames, the $stacktrace name (§20.17.2) -- binds the arguments
// (§13.5) and answers true, `call` naming the object, the task and its class.
// A static task, named through a handle or through the class scope (§8.10,
// §8.23), is set up the same way with no `this`, `call.obj` null. Answers
// false, having pushed nothing, for any other call: a function, a module task,
// a handle holding no object. The body is then run by ExecInstanceTaskCall in
// stmt_exec_class_task.cpp, and TeardownInstanceTaskCall writes the output
// arguments back (§13.5.2) and pops what the setup pushed, in reverse.
//
// §13.5.5 makes the empty parentheses optional after the name of a class
// method, so the statement `h.t;` is the call `h.t();` and a bare `t;` inside
// a method of the object's class is `t();` (§8.13); either is set up here as
// the parenthesised call is, the statement's expression standing as the call
// with no actuals.
bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call);
void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena);

// §13.5.5 with §8.6: an expression statement that is a class method named
// without the parentheses -- `h.m;` through a handle, or a bare `m;` inside a
// method of the object's class (§8.13) -- calls the method, dispatched as the
// parenthesised call is (a virtual method by the object's class, §8.20), and
// discards its result; any other expression is evaluated as it stands. The
// statement executor calls this for an expression statement that is no task
// call, in place of evaluating the expression.
void ExecCallStmtExpr(const Expr* expr, SimContext& ctx, Arena& arena);

// §13.5.5 (printed page 351): a class function method whose formals, if any,
// all have defaults is called by its name alone wherever its value is read,
// not only as a statement -- a bare `m` inside a method of the class, `C::m`
// or `T::m` through the class scope, `h.m` through a handle -- as the call
// with the empty parentheses would be. True with the call's value in `out`
// when `expr` is such a name; false, having evaluated nothing, otherwise.
bool TryEvalParenFreeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

}  // namespace delta
