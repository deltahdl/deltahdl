#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;

// A.8.2: a tf_call names a task or a function. Reports each call in the
// procedures `decl` declares whose name, written alone, the module or a block
// around the call declares as a variable or a net (§23.9): a bare call
// statement, `x;`, and a call with an argument list wherever a statement
// holds one, `x();` or `y = x(1);`. A.6.9: reports too a call statement
// naming a let, a sequence, a property, or a variable or a net `unit`'s
// packages declare and the module imports, which only an expression may name.
void ReportCallsOfDataNames(const ModuleDecl& decl, const CompilationUnit& unit,
                            DiagEngine& diag);

}  // namespace delta
