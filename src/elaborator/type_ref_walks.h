#pragma once

#include <functional>

#include "common/source_loc.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct ClassDecl;
struct CompilationUnit;
struct ModuleItem;

// Resolves, in place, the type reference a declaration's type holds, written
// at the given position, where its argument names nothing the procedure
// declares: a module's, a class's, a package's or the compilation unit's
// resolution of the names it declares.
using TypeRefResolver = std::function<void(DataType&, SourceLoc)>;

// §6.23 with A.2.7, A.2.8 and A.6.8: the type references of the subroutine or
// procedural block `item`, resolved in place: its formals' types, the types of
// the variables its blocks declare and those of the variables its for loops
// declare. A name the procedure declares hides those of the scope around it
// (§23.9), so a reference to one takes the type, and the unpacked dimensions,
// of its latest declaration in scope; any other is left to `resolve_outer`.
// A.2.5: a formal's or a block variable's associative index written as a type
// reference, `[type(k)]`, takes its type the same way, in `arena`, the
// dimension's type_value.
void ResolveProceduralTypeRefs(ModuleItem* item,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena);

// §6.23 with §8.5 and §23.9: the type references of the class `cls`,
// resolved in place: its properties' types and their associative indexes
// written as type references (A.2.5), whose types are made in `arena`, those
// its methods write (ResolveProceduralTypeRefs), and those of the classes
// nested in it. A name the class declares as a property is the class's own,
// over the scope around it, which `resolve_outer` resolves any other name in.
void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          Arena& arena);

// §6.23 with §26.2 and §3.12.1: the type references a package or the
// compilation unit writes outside its modules, resolved in place against the
// scope's own declarations (ResolveScopeTypeRef): the types of each package's
// and the unit's typedefs and nettypes, its variables' associative indexes
// written as type references (A.2.5), and those their subroutines and classes
// write. They are resolved ahead of the typedefs' registration, which
// records the type each typedef names.
void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena);

}  // namespace delta
