#include "elaborator/interface_syntax.h"

namespace delta {

bool InterfacePortHierRefIsLegal(
    const std::vector<InterfaceHierRefStep>& path) {
  // A reference that names nothing cannot designate an interface instance.
  if (path.empty()) {
    return false;
  }
  // No step may resolve through an arrayed instance element or a generate
  // block; either makes the reference ambiguous as an interface-port actual.
  for (auto step : path) {
    if (step == InterfaceHierRefStep::kArrayedInstanceElement ||
        step == InterfaceHierRefStep::kGenerateBlock) {
      return false;
    }
  }
  // The reference must ultimately land on an interface instance.
  return path.back() == InterfaceHierRefStep::kInterfaceInstance;
}

bool ArrayedInterfaceDefparamIsLegal(bool instance_has_arrayed_interface_actual,
                                     DefparamReach reach) {
  // The restriction only bites for an instance whose port actuals refer to an
  // arrayed interface; there, the defparam must stay within the instance.
  return !instance_has_arrayed_interface_actual ||
         reach != DefparamReach::kOutsideInstance;
}

}  // namespace delta
