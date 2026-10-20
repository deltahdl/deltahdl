#pragma once

#include <functional>
#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct RtlirDesign;
struct RtlirNet;
struct VpiObject;

// What a pass over the nets of a design does with one: the net, the object
// the run built for it, or for one of its elements where it is an array net
// of one unpacked dimension, and the path of the instance declaring it.
using VpiDeclaredNetVisit = std::function<void(
    const RtlirNet& net, VpiObject& obj, const std::string& prefix)>;

// Calls `visit` for each net each instance of `design`, which is not null,
// declares and the run built an object for, a net standing for an enclosing
// module's (§23.4) being passed over.
void ForEachDeclaredNetObject(const RtlirDesign* design,
                              const VpiObjectMap& objects,
                              const VpiDeclaredNetVisit& visit);

// §37.16 (figure): tell each net of `design`, which is not null, the scalared
// or vectored keyword and the drive strengths its declaration writes.
void RecordNetDeclarationFacts(const RtlirDesign* design,
                               const VpiObjectMap& objects);

}  // namespace delta
