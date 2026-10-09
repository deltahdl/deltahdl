#pragma once

#include <string_view>
#include <unordered_map>

#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "simulator/vpi_object.h"

namespace delta {

// §34.5.32.2: give the object each viewport of a decryption envelope names, in
// every instance holding it, the access the viewport asks of §37.3.6's
// protection, where the access is one this tool defines. Run once the design's
// objects are marked protected, under the flat names they are keyed by, with
// the source description of the run the context is attached to, which holds
// the viewports its reading met.
void RecordViewportGrants(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager& sources);

}  // namespace delta
