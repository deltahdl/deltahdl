#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct VpiObject;

VpiObject* VpiCollectionElement(VpiObject& array, int index,
                                const VpiAttachBuild& build);

void VpiRefreshElementCopy(VpiObject& element);

void VpiStoreElementCopy(VpiObject& element);

}  // namespace delta
