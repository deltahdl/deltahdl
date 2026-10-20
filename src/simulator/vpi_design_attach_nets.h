#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

// §37.16 (figure): tell each net of `design`, which is not null, the scalared
// or vectored keyword and the drive strengths its declaration writes.
void RecordNetDeclarationFacts(const RtlirDesign* design,
                               const VpiObjectMap& objects);

// §37.16 detail 32: make the subelements of each packed array net of
// `design`, which is not null, one packed dimension at a time down to its
// struct, union or enum nets, which its vpiElement iteration reaches.
void AttachPackedArrayNetElements(const RtlirDesign* design,
                                  const VpiObjectMap& objects, SimContext& ctx,
                                  const VpiAttachBuild& build);

}  // namespace delta
