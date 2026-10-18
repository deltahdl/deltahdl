#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

// §37.6 and §37.8 with §25.7: give each interface instance an interface tf
// decl per task or function it declares extern, or a modport of it exports,
// whose definition a connected module gives (§25.7.3). Each reaches the task or
// function `made` holds for that definition, none where no module defines it,
// and reports vpiExternAcc; a task declared extern forkjoin (§25.7.4) is one
// decl per definition, each reporting vpiForkJoinAcc (§37.8 detail 1). Which
// instance defines each one is read from the run `ctx`.
void AttachInterfaceTfDecls(const RtlirDesign* design,
                            const VpiObjectMap& objects,
                            const VpiSubroutineObjects& made, SimContext& ctx,
                            const VpiAttachBuild& build);

}  // namespace delta
