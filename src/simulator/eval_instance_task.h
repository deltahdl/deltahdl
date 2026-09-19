#pragma once

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
// Answers false, having pushed nothing, for any other call: a function, a
// static task (§8.10, run in class scope by the evaluator), a module task, a
// handle holding no object. The body is then run by ExecInstanceTaskCall in
// stmt_exec_class_task.cpp, and TeardownInstanceTaskCall writes the output
// arguments back (§13.5.2) and pops what the setup pushed, in reverse.
bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call);
void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena);

}  // namespace delta
