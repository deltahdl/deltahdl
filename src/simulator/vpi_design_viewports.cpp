#include "simulator/vpi_design_viewports.h"

#include <string>
#include <string_view>
#include <unordered_map>

#include "common/envelope_viewport.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "elaborator/viewport_resolution.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

void RecordViewportGrants(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager& sources) {
  if (design == nullptr || design->compilation_unit == nullptr) return;
  for (const EnvelopeViewport& viewport : sources.Viewports()) {
    const ViewportAccess kAccess = ViewportAccessOf(viewport.access);
    if (kAccess == ViewportAccess::kNone) continue;
    auto target = ResolveViewport(*design->compilation_unit, viewport, sources);
    if (!target) continue;
    // The name was resolved against the design element's declarations, so it
    // names the same object in each instance of the element.
    WalkInstancePaths(
        design, [&](const RtlirModule* mod, const std::string& prefix) {
          if (mod->name != target->definition) return;
          VpiHandle obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, target->path));
          if (obj != nullptr) obj->viewport_access = kAccess;
        });
  }
}

}  // namespace delta
