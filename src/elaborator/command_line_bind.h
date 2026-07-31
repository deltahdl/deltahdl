#pragma once

#include <string_view>
#include <vector>

namespace delta {

class DiagEngine;
class Elaborator;
struct CompilationUnit;
struct ConfigDecl;
struct RtlirDesign;

// §33.5.4: what a command line settles before any binding starts, whichever
// use model assembled the compilation unit it settles it over.
//
// Two things are settled. The first is which rules bind the design's
// instances: a configuration's own rules, or else the default rules the
// library map file carries. The second is which cells root the design.
//
// A configuration is put in force by naming its source description among the
// files on the command line, so the configuration governing a run is one the
// compilation unit already holds rather than something the tool has to be told
// about separately. A configuration in force then settles the roots outright,
// through the design statement it carries: the cell that statement names is
// the top-level one, and the cells the rest of the named files declare and no
// instance names root nothing beside it. Those cells are top-level cells
// (§23.3.1) only of a run that put no configuration in force.

// The configurations a command line put in force over `unit`: those it holds
// that name a design, less any that another configuration delegates an
// instance to. A configuration delegated to describes a subtree of the design
// that delegates to it rather than a design of its own, so it roots nothing.
//
// The result is empty when the command line named no configuration source
// description, and holds more than one when it named more than one whole
// design. Nothing in the unit says which of those was meant, so settling that
// is left to the caller.
std::vector<const ConfigDecl*> ConfigsInForce(const CompilationUnit& unit);

// Elaborates the design the command line describes and returns it, or nullptr
// having reported.
//
// With a configuration in force the design is the one its design statement
// names, bound under that configuration's rules. `top` is not consulted there,
// because the design statement is what says which cell is the top-level one.
// With none in force the design is rooted at the cell `top` names, or -- when
// the command line named no top-level cell either, leaving `top` empty -- at
// every cell no instance names, bound under the library map's default rules.
RtlirDesign* ElaborateCommandLine(Elaborator& elab, const CompilationUnit& unit,
                                  std::string_view top, DiagEngine& diag);

}  // namespace delta
