#pragma once

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scopes.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

inline VpiHandle ChildNamed(VpiHandle parent, std::string_view name) {
  for (auto* child : parent->children) {
    if (child->name == name && child->type != vpiAttribute) return child;
  }
  for (auto* child : parent->children) {
    const std::size_t kLength = child->name.size();
    if (kLength > 0 && name.size() > kLength && name.starts_with(child->name) &&
        name[kLength] == '[') {
      return ChildNamed(child, name);
    }
  }
  return VpiNestedScopeNamed(parent, name);
}

inline VpiHandle VpiGenScopeOf(VpiHandle instance, const HierPath& path) {
  VpiHandle scope = instance;
  for (const HierStep& step : path) {
    if (scope == nullptr) return nullptr;
    std::string name(step.external_name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    scope = ChildNamed(scope, name);
  }
  return scope;
}

inline bool VpiIndexSelects(const VpiObject& holder, const VpiObject& child,
                            int index) {
  return child.type != vpiRange && child.type != vpiConstant &&
         child.type != vpiGenVar && child.type != vpiAttribute &&
         !VpiIsTypespecType(child.type) && child.type != vpiOperation &&
         child.type != vpiParamAssign && child.type != vpiVarSelect &&
         child.type != vpiPrimTerm && child.type != vpiForce &&
         (child.type != vpiPort || child.parent == &holder) &&
         child.instance_facts.array_indices.size() <= 1 && child.index == index;
}

inline VpiHandle ObjectNamedIn(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    VpiHandle scope, std::string_view name) {
  if (scope != nullptr) return ChildNamed(scope, name);
  auto it = objects.find(name);
  return it == objects.end() ? nullptr : it->second;
}

inline std::unordered_set<std::string_view> VpiDottedEscapedNames(
    const RtlirDesign* design) {
  if (design == nullptr || design->compilation_unit == nullptr) return {};
  return design->compilation_unit->dotted_escaped_names;
}

inline VpiHandle FindObjectBelow(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    VpiHandle scope, std::string_view rest) {
  for (std::size_t end = 0;; ++end) {
    end = std::min(rest.find('.', end), rest.size());
    VpiHandle found = ObjectNamedIn(objects, scope, rest.substr(0, end));
    if (end == rest.size()) return found;
    if (found == nullptr) continue;
    VpiHandle below = FindObjectBelow(objects, found, rest.substr(end + 1));
    if (below != nullptr) return below;
  }
}

inline VpiHandle FindObjectForFlatName(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    std::string_view flat_name) {
  return FindObjectBelow(objects, nullptr, flat_name);
}

struct VpiUnitScope {
  const CompilationUnit* unit;
  VpiObject* scope;
  int index;
};

inline std::vector<VpiUnitScope> VpiUnitScopes(
    const RtlirDesign& design,
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  std::vector<VpiUnitScope> units;
  units.reserve(design.compilation_units.size());
  for (std::size_t k = 0; k < design.compilation_units.size(); ++k) {
    const int kIndex = static_cast<int>(k);
    units.push_back(
        {design.compilation_units[k],
         FindObjectForFlatName(objects, UnitScopes::ScopeName(kIndex)),
         kIndex});
  }
  if (units.empty() && design.compilation_unit != nullptr) {
    units.push_back({design.compilation_unit,
                     FindObjectForFlatName(objects, UnitScopes::ScopeName(-1)),
                     -1});
  }
  return units;
}

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

inline int VpiInstanceKind(const RtlirModule* mod) {
  if (mod->is_interface) return vpiInterface;
  if (mod->is_program) return vpiProgram;
  return kVpiModule;
}

inline std::string VpiFlatName(const std::string& prefix,
                               std::string_view name) {
  if (prefix.empty()) return std::string(name);
  return prefix + "." + std::string(name);
}

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

inline VpiHandle VpiChildInstanceObject(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    VpiHandle parent, const std::string& path, const RtlirModuleInst& child) {
  if (VpiHandle flat = FindObjectForFlatName(objects, path)) return flat;
  return ChildNamed(
      VpiGenScopeOf(parent, child.gen_block_path),
      child.gen_block_path.empty() ? child.inst_name : child.simple_inst_name);
}

template <typename Visit>
void WalkInstanceObjects(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    Visit visit) {
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  std::vector<std::tuple<const RtlirModule*, std::string, VpiHandle>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) {
    const bool kFirst = top == design->top_modules.front();
    work.emplace_back(top, kFirst ? std::string() : std::string(top->name),
                      FindObjectForFlatName(objects, top->name));
  }
  while (!work.empty()) {
    auto [mod, prefix, object] = std::move(work.back());
    work.pop_back();
    if (mod == nullptr) continue;
    for (const auto& child : mod->children) {
      std::string path = VpiFlatName(prefix, child.inst_name);
      VpiHandle found = VpiChildInstanceObject(objects, object, path, child);
      work.emplace_back(child.resolved, std::move(path), found);
    }
    visit(mod, prefix, object);
  }
}

}  // namespace delta
