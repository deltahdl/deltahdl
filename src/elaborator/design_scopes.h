#pragma once

#include <string>
#include <vector>

#include "elaborator/rtlir.h"

namespace delta {

// Annex D.11 has the argument of $scope be "the complete hierarchical name of
// a module, task, function, or named block", and D.6's $list takes the same.
// These are the complete hierarchical names of every such scope of the
// elaborated design: each top-level module and each instance under it by its
// instance path, each task and function declared in one by that path and its
// name, and each named block of a procedure by the path and the labels of the
// blocks it stands in.
std::vector<std::string> CompleteHierarchicalScopeNames(
    const RtlirDesign* design);

}  // namespace delta
