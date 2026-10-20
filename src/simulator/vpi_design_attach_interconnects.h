#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

// §37.24 (figure) and details 1 and 2 with §6.6.8: give each generic
// interconnect a module's body declares a level of interconnect arrays per
// dimension it was declared with - the unpacked ones outermost and not packed,
// the packed ones inside them and packed - down to an interconnect net per
// index of the last, each level reaching the ranges of its dimensions and the
// bounds of its first. Where the run keys a net under an element's name, as it
// does each net of a one-dimensional array, that net is the element.
void AttachInterconnects(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build);

// §37.24: the same for the net each interconnect port stands for, its lowConn
// (§37.14), once VpiContext::AttachDesignPorts has made it.
void AttachInterconnectPorts(const RtlirDesign* design,
                             const VpiObjectMap& objects, SimContext& ctx,
                             const VpiAttachBuild& build);

// §37.24 detail 1: give each interconnect net of an instance the typespec of
// the net a port connects it to (VpiConnectedNet) and, where that is an array
// or a struct or union, an interconnect net per element or member, which its
// vpiElement or vpiMember iteration reaches.
void AttachInterconnectTypespecs(const RtlirDesign* design,
                                 const VpiObjectMap& objects,
                                 const VpiAttachBuild& build);

}  // namespace delta
