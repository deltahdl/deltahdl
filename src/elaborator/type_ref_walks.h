#pragma once

#include <functional>
#include <span>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

// A name a procedure declares, with the type and unpacked dimensions it was
// declared with.
struct ProceduralLocal {
  std::string_view name;
  const DataType* type;
  const std::vector<Expr*>* unpacked_dims;
};

// Resolves, in place, the type reference a declaration's type holds, written
// at the given position, where its argument is no name the procedure
// declares: a module's, a class's, a package's or the compilation unit's
// resolution of the names it declares. The names the procedure declares ahead
// of the declaration, latest last, are given with it, empty for a declaration
// no procedure writes, since a `.` written after one of them selects a member
// of the procedure's value (§6.21). Answers the unpacked dimensions of the
// array the reference names, which a declaration takes inside those it writes
// (§7.4.4), and none where it names no unpacked array.
using TypeRefResolver = std::function<std::vector<Expr*>(
    DataType&, SourceLoc, std::span<const ProceduralLocal>)>;

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
// resolved in place: its properties' types, the associative indexes its
// properties and typedefs write as type references (A.2.5), whose types are
// made in `arena`, those its methods write (ResolveProceduralTypeRefs), and
// those of the classes nested in it. A name the class declares as a property,
// or inherits as one from a class it extends that `unit` declares (§8.13),
// written bare or selected of `this` (§8.11), is the class's own, over the
// scope around it, and stands for the property's type and unpacked
// dimensions; `resolve_outer` resolves any other name.
void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          const CompilationUnit* unit, Arena& arena);

// §6.23 with §26.2 and §3.12.1: the type references a package or the
// compilation unit writes outside its modules, resolved in place against the
// scope's own declarations (ResolveScopeTypeRef): the types of each package's
// and the unit's typedefs and nettypes, its typedefs' and variables'
// associative indexes written as type references (A.2.5), and those their
// subroutines and classes write. They are resolved ahead of the typedefs'
// registration, which records the type each typedef names.
void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena);

}  // namespace delta
