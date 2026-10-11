#pragma once

#include <string_view>

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;

// §8.25: the parameter of `cls` declared without a default, which leaves the
// class no default specialization; empty where every parameter has one. A
// type parameter's default is a type, held in ClassDecl::param_types beside
// its entry in params and kImplicit where none was written (§6.20.3).
std::string_view ParameterWithoutDefault(const ClassDecl& cls);

// §8.25: reports each use of a parameterized class's unadorned name as a data
// type where the class has no default specialization, because one of its
// parameters, a value or a type parameter, has no default. The uses are every
// declaration the unit writes a type in: a variable's, a class property's, a
// subroutine argument's and return type, a typedef's, and the class an
// `extends` clause names without arguments. A variable a module, interface,
// program or checker declares among its items is left to
// Elaborator::ValidateVarDeclTypes, which judges it per instance, after a type
// parameter written as its type has taken the instance's override.
void ReportUnadornedClassesWithoutDefaults(const CompilationUnit& unit,
                                           DiagEngine& diag);

}  // namespace delta
