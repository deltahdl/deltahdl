#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

// §6.6.7 (printed page 97): a user-defined nettype names a data type as a
// typedef does, but may be used only to declare a net. Reports `nettype` named
// as the type of `use`, which is no net.
void ReportNettypeNotNet(std::string_view nettype, std::string_view use,
                         SourceLoc loc, DiagEngine& diag);

// Reports each place in the module `decl`, and in any class it declares, that
// names one of `nettypes` as a data type without declaring a net, a nettype
// written through a package or `$unit` being looked up under its NamedTypeKey
// (src/elaborator/net_data_type.h), "P::nt" or "$unit::nt": a member of a
// structure or union, a function's return, a subroutine's argument, a
// parameter, a cast, a variable a procedural block declares and a class
// property. Within a begin-end block, a fork-join block, a subroutine body or
// a class, the nettypes that scope declares for itself are judged by their
// bare names as well, and a nettype a class of `decl`, of `unit` or of one of
// its packages declares is judged by its "C::nt" key everywhere. A data
// declaration among the module's items is judged as it is elaborated instead,
// since naming a nettype makes it a net's unless it is written with `var`,
// `const` or `static`; one naming a class's nettype through the class's scope
// is reported here, since A.2.1.3 writes a net with a bare nettype name. A
// packed dimension written after a nettype's name is reported too, on a port
// (A.2.2.1) and on a declaration (A.2.1.3), since a net of a nettype takes the
// nettype's data type.
void CheckNettypeUses(const ModuleDecl* decl, const CompilationUnit& unit,
                      const std::unordered_set<std::string_view>& nettypes,
                      DiagEngine& diag);

// A.2.1.3: whether `item` opens with `var`, `const` or `static`, which begin a
// data declaration and never a net declaration, so that naming a nettype in it
// declares a variable. The parser refuses `automatic` outside procedural code.
bool WrittenAsDataDeclaration(const ModuleItem* item);

// The same report for the compilation unit's items and classes and for each
// package's items, which no module's elaboration reaches: a nettype named
// anywhere a module's is reported, and as the type of a variable declared at
// that scope. Each scope is judged against the nettypes it declares itself for
// a bare name, against `scoped`, the nettypes recorded under their "P::nt"
// keys, for a name written through a package, and against the nettypes the
// unit's and the packages' classes declare for a name written through a
// class's scope, which declares a variable however the item is written.
void CheckUnitNettypeUses(const CompilationUnit* unit,
                          const std::unordered_set<std::string_view>& scoped,
                          DiagEngine& diag);

}  // namespace delta
