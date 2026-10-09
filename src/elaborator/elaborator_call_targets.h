#pragma once

namespace delta {

class DiagEngine;
struct ModuleDecl;

// A.8.2: a tf_call names a task or a function. Reports each call in the
// procedures `decl` declares whose name, written alone, the module or a block
// around the call declares as a variable or a net (§23.9): a bare call
// statement, `x;`, and a call with an argument list wherever a statement
// holds one, `x();` or `y = x(1);`.
void ReportCallsOfDataNames(const ModuleDecl& decl, DiagEngine& diag);

}  // namespace delta
