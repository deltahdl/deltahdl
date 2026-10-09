#pragma once

#include <functional>
#include <string_view>

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;

// A.8.2 and A.6.9: a tf_call names a task or a function. Reports each call in
// the procedures `decl` declares whose name, written alone, the module or a
// block around the call declares as a variable or a net (§23.9), whether a
// call statement, `x;` or `x();`, or a call within an expression,
// `y = x(1);`; and each call statement naming no task or function the module,
// the compilation unit `unit` or a package either imports from declares. A
// call statement naming something the scope does not see at all, which
// `visible` answers, is reported as an undeclared identifier where it has an
// argument list, a bare one being reported by the scope rules already.
void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag);

}  // namespace delta
