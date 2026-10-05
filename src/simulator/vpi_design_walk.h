#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
//
// §37.17: an element of an array var hangs from the array, a subarray's from
// the subarray, and a bit from its vector, each named with its indices, so a
// name such as `arr[1][2]` is found under the child whose name it extends by an
// index.
inline VpiHandle ChildNamed(VpiHandle parent, std::string_view name) {
  for (auto* child : parent->children) {
    if (child->name == name) return child;
  }
  for (auto* child : parent->children) {
    const std::size_t kLength = child->name.size();
    if (kLength > 0 && name.size() > kLength && name.starts_with(child->name) &&
        name[kLength] == '[') {
      return ChildNamed(child, name);
    }
  }
  return nullptr;
}

// §27.4 with §37.12: the generate block instance the block path `path` names
// below `instance`, outermost first, each step named by its block's name and,
// in a loop generate, its index; the instance itself for an empty path, and
// null where a block on the path has no object.
inline VpiHandle VpiGenScopeOf(VpiHandle instance, const HierPath& path) {
  VpiHandle scope = instance;
  for (const HierStep& step : path) {
    if (scope == nullptr) return nullptr;
    std::string name(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    scope = ChildNamed(scope, name);
  }
  return scope;
}

// Whether `child` is the sub-object an index select of `index` names (§38.19).
// A range object describes a dimension (§37.22) and an index constant locates
// its holder (§37.17 details 13 and 18), so no index selects either.
inline bool VpiIndexSelects(const VpiObject& child, int index) {
  return child.type != vpiRange && child.type != vpiConstant &&
         child.index == index;
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

// §37.6, §37.9 and §37.10: the object type an instance of `mod` is -- an
// interface, a program or a module, as its definition is.
inline int VpiInstanceKind(const RtlirModule* mod) {
  if (mod->is_interface) return vpiInterface;
  if (mod->is_program) return vpiProgram;
  return kVpiModule;
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
// flat instance path the simulator keys that scope's objects under. The first
// top carries the empty prefix, having no instantiation over it to be named
// by; a later one is keyed under its own name, as Lowerer::LowerParallelTop
// lowers it.
template <typename Visit>
void WalkInstancePaths(const RtlirDesign* design, Visit visit) {
  std::vector<std::pair<const RtlirModule*, std::string>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) {
    bool first = top == design->top_modules.front();
    work.emplace_back(top, first ? std::string() : std::string(top->name));
  }

  while (!work.empty()) {
    auto [mod, prefix] = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    PushChildInstances(mod, prefix, work);
    visit(mod, prefix);
  }
}

}  // namespace delta
