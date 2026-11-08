#pragma once

#include <string_view>
#include <unordered_map>

#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "simulator/vpi_object.h"

namespace delta {

void RecordViewportGrants(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager& sources);

}  // namespace delta
