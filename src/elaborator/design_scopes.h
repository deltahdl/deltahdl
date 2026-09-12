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

// Annex D.13 has $showvars report the reg and net variables of the current
// scope. These are the ones each module instance of the elaborated design
// declares, under the instance's complete hierarchical name as above: the
// prefix the simulator keys the instance's variables by, empty for a
// top-level module and the instance path below one with its trailing dot, and
// the declared names, nets before variables, each in declaration order.
struct ScopeDeclaredVariables {
  std::string scope;
  std::string prefix;
  std::vector<std::string> names;
};
std::vector<ScopeDeclaredVariables> ModuleInstanceVariables(
    const RtlirDesign* design);

}  // namespace delta
