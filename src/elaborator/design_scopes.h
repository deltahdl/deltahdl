#pragma once

#include <string>
#include <vector>

#include "elaborator/rtlir.h"

namespace delta {

std::vector<std::string> CompleteHierarchicalScopeNames(
    const RtlirDesign* design);

struct ScopeDeclaredVariables {
  std::string scope;
  std::string prefix;
  std::vector<std::string> names;
};
std::vector<ScopeDeclaredVariables> ModuleInstanceVariables(
    const RtlirDesign* design);

}  // namespace delta
