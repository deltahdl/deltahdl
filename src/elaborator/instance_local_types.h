#pragma once

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;

// §6.22 (printed pages 134-137): the scope of a data type identifier includes
// the hierarchical instance scope, so each instance of a module that declares
// a type has a type of its own, and the types two instances declare by one
// declaration neither match nor are equivalent. Reports each assignment in the
// module `decl` between two variables reached through different instances,
// `s1.v = s2.v`, whose types are each declared by the instance's module, by a
// typedef or in place, and are an unpacked structure or union, an enumeration
// or a class: types that §6.22.3 lets no assignment cross unless they are
// equivalent. A packed structure or union is equivalent to its counterpart
// whatever instance declares it, and a type from a package, the compilation
// unit or a type parameter is shared by both instances, so neither is reported.
void CheckInstanceLocalTypeAssignments(const ModuleDecl* decl,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag);

}  // namespace delta
