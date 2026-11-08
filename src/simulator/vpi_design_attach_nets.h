#pragma once

#include <functional>
#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct RtlirDesign;
struct RtlirNet;
struct VpiObject;

using VpiDeclaredNetVisit = std::function<void(
    const RtlirNet& net, VpiObject& obj, const std::string& prefix)>;

void ForEachDeclaredNetObject(const RtlirDesign* design,
                              const VpiObjectMap& objects,
                              const VpiDeclaredNetVisit& visit);

void RecordNetDeclarationFacts(const RtlirDesign* design,
                               const VpiObjectMap& objects);

}  // namespace delta
