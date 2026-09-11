#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"

// §36.10: how a pass that has something to say about an elaborated design finds
// the objects the run built for it. "VPI routines provide access to objects in
// an instantiated SystemVerilog design. An instantiated design is one where
// each instance of an object is uniquely accessible", and the simulator makes
// each one uniquely accessible by keying it on the flat path of the instance it
// belongs to. These four are what a walk of the design turns that path into an
// object with. They live in a header of their own because more than one file
// carries such a pass: the passes that build the objects are in
// vpi_design_attach.cpp and the ones that describe an already-built object are
// in vpi_helpers_instance.cpp, and a copy in each would be two answers to one
// question.

namespace delta {

// The child of `parent` carrying this name, or null where it has none. §36.10
// makes each instance's objects "uniquely accessible", so one component of a
// flat name is matched against the children of the scope reached so far rather
// than against every object of the design.
inline VpiHandle ChildNamed(VpiHandle parent, std::string_view name) {
  for (auto* child : parent->children) {
    if (child->name == name) return child;
  }
  return nullptr;
}

// The object a flat design name already stands for, and null where the name
// reaches none. VpiContext::DesignObjectForFlatName makes the scopes it passes
// through; this one makes nothing, which is what a reader that has something to
// say about an object the run built wants: a declaration the run built no
// object for is passed over rather than given an empty one.
inline VpiHandle FindObjectForFlatName(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    std::string_view flat_name) {
  std::vector<std::string_view> parts = VpiNamePathComponents(flat_name);
  if (parts.empty()) return nullptr;

  auto root = objects.find(parts.front());
  if (root == objects.end()) return nullptr;

  VpiHandle current = root->second;
  for (std::size_t i = 1; i < parts.size() && current != nullptr; ++i) {
    current = ChildNamed(current, parts[i]);
  }
  return current;
}

// The instances `mod` holds, pushed onto the walk under their own paths. An
// instance's path is its parent's with its name on the end, which is the string
// the simulator keys every object of that instance under.
inline void PushChildInstances(
    const RtlirModule* mod, const std::string& prefix,
    std::vector<std::pair<const RtlirModule*, std::string>>& work) {
  work.reserve(work.size() + mod->children.size());
  for (const auto& child : mod->children) {
    std::string child_prefix = prefix;
    if (!child_prefix.empty()) child_prefix += '.';
    child_prefix += std::string(child.inst_name);
    work.emplace_back(child.resolved, child_prefix);
  }
}

// The flat name the simulator keys one declaration of this scope under: the
// instance path with the declared name on the end. A top module carries the
// empty prefix and keys its own declarations under their bare names.
inline std::string VpiFlatName(const std::string& prefix,
                               std::string_view name) {
  if (prefix.empty()) return std::string(name);
  return prefix + "." + std::string(name);
}

// Every scope of the design, visited outward from each top module under the
// flat instance path the simulator keys that scope's objects under. A top
// carries the empty prefix, having no instantiation over it to be named by.
template <typename Visit>
void WalkInstancePaths(const RtlirDesign* design, Visit visit) {
  std::vector<std::pair<const RtlirModule*, std::string>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) work.emplace_back(top, std::string());

  while (!work.empty()) {
    auto [mod, prefix] = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    PushChildInstances(mod, prefix, work);
    visit(mod, prefix);
  }
}

}  // namespace delta
