#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;

// A.8.2 and A.6.9: a tf_call names a task or a function. Reports each call in
// the procedures `decl` declares whose name, written alone, the module or a
// block around the call declares as a variable or a net (§23.9), whether a
// call statement, `x;` or `x();`, or a call within an expression,
// `y = x(1);`; and each call statement naming something else the module
// declares, or imports from a package of `unit` as data, other than a task or
// a function, such as a parameter, a let or a sequence. A name the module does
// not declare may name a subroutine of an instance above it (§23.8).
void ReportCallsOfDataNames(const ModuleDecl& decl, const CompilationUnit& unit,
                            DiagEngine& diag);

}  // namespace delta
