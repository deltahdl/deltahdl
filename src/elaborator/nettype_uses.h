#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"

namespace delta {

struct ModuleDecl;

// §6.6.7 (printed page 97): a user-defined nettype names a data type as a
// typedef does, but may be used only to declare a net. Reports `nettype` named
// as the type of `use`, which is no net.
void ReportNettypeNotNet(std::string_view nettype, std::string_view use,
                         SourceLoc loc, DiagEngine& diag);

// Reports each place in the module `decl`, and in any class it declares, that
// names one of `nettypes` as a data type without declaring a net: a member of a
// structure or union, a function's return, a subroutine's argument, a
// parameter, a cast, a variable a procedural block declares and a class
// property. A data declaration among the module's items is judged as it is
// elaborated instead, since naming a nettype makes it a net's unless it is
// written with `var`, `const` or `static`.
void CheckNettypeUses(const ModuleDecl* decl,
                      const std::unordered_set<std::string_view>& nettypes,
                      DiagEngine& diag);

}  // namespace delta
