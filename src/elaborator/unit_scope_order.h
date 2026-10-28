#pragma once

#include <string_view>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

// Whether position `a` stands before position `b`. The preprocessor joins the
// sources of a compilation unit into one text, so two positions of one unit
// are ordered by line and then column.
bool PrecedesInText(SourceLoc a, SourceLoc b);

// §3.12.1 with §6.21: whether the compilation-unit scope declares `name` as a
// variable or a net before `reference`, one of the items written outside every
// design element. The unit's items are asked for a data declaration rather
// than every named item, so a unit function's or class's name is not one.
bool UnitDeclaresData(const CompilationUnit* unit, std::string_view name,
                      SourceLoc reference);

// §3.12.1 (printed pages 56-57): a reference searches only the portion of the
// compilation-unit scope written before it. Whether the unit declares `name`
// as a variable or a net after `reference` and declares nothing of that name
// before it, so that the reference does not reach the unit's declaration.
bool UnitDataDeclaredOnlyAfter(const CompilationUnit* unit,
                               std::string_view name, SourceLoc reference);

// §3.12.1 (printed page 57): other than a task's or a function's name, a
// reference names only what the compilation unit has already declared. Whether
// the unit declares `name` as a parameter or an enumeration constant after
// `reference` and declares nothing of that name before it.
bool UnitConstantDeclaredOnlyAfter(const CompilationUnit* unit,
                                   std::string_view name, SourceLoc reference);

// §3.12.1: whether `decl` declares `name` itself, so that a declaration of the
// name the compilation unit writes after it is not what the module's reads
// reach: a parameter of its header, a port, an item, or an enumeration
// constant an item's type declares (§6.19).
bool ModuleDeclaresName(const ModuleDecl* decl, std::string_view name);

// §3.12.1 (printed page 56): the items of the compilation-unit scope written
// before `reference`, the portion of the scope a reference there searches.
std::vector<ModuleItem*> UnitItemsBefore(const CompilationUnit* unit,
                                         SourceLoc reference);

// §3.12.1 (printed page 57): `$unit::name` selects a declaration of the
// compilation-unit scope and lets a reference refer forward no further than
// the bare name does, a task's or a function's name being the one that may
// be declared after its reference. Reports each `$unit::` name read in the
// bodies, assignments and initializers of `items` that names a declaration of
// the unit written after it, or no declaration of the unit at all.
void ReportUnitScopedReferences(const std::vector<ModuleItem*>& items,
                                const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
