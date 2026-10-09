#pragma once

#include <functional>
#include <string_view>
#include <unordered_set>

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;

// §23.8: the tasks and functions the modules of `unit` that instantiate
// `module`, directly or through instances between, declare, which a call the
// module writes by a name it does not declare may name.
std::unordered_set<std::string_view> EnclosingSubroutineNames(
    const CompilationUnit& unit, std::string_view module);

// A.8.2 and A.6.9: a tf_call names a task or a function. Reports each call in
// the procedures `decl` declares whose name, written alone, the module or a
// block around the call declares as a variable or a net (§23.9), whether a
// call statement, `x;` or `x();`, or a call within an expression,
// `y = x(1);`; each call statement naming something else the module declares,
// or imports from a package of `unit` as data, other than a task or a
// function, such as a parameter, a let or a sequence; and each call statement
// with an argument list naming nothing `visible` says the module's scope, the
// compilation unit or a module enclosing an instance of it sees (§23.8), as an
// undeclared identifier.
void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag);

}  // namespace delta
