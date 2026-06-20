#include "simulator/vpi.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {


VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
}

VpiHandle VpiContext::AllocObject() {
  auto* obj = new VpiObject();
  all_objects_.push_back(obj);
  return obj;
}

// §37.3.7: derive the reported allocation scheme from how the object was
// allocated. Frame/thread allocations are Automatic, dynamic-memory (class)
// allocations are Dynamic, and everything else falls through to the mandated
// Other default.
int VpiAllocSchemeFor(VpiAllocKind kind) {
  switch (kind) {
    case VpiAllocKind::kFrameOrThread:
      return kVpiAutomaticScheme;
    case VpiAllocKind::kDynamic:
      return kVpiDynamicScheme;
    case VpiAllocKind::kOther:
      return kVpiOtherScheme;
  }
  return kVpiOtherScheme;
}

// §37.10 details 1 and 10: keep only the entries that are user-defined and
// explicitly declared in the instance, in their original order. Built-in
// definitions and entries merely made visible (e.g. by import) are dropped.
static std::vector<const VpiTypeDeclEntry*> FilterDeclaredUserEntries(
    const std::vector<VpiTypeDeclEntry>& entries) {
  std::vector<const VpiTypeDeclEntry*> visible;
  for (const auto& entry : entries) {
    if (entry.user_defined && entry.declared_in_instance) {
      visible.push_back(&entry);
    }
  }
  return visible;
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

bool VpiIsInstanceType(int type) {
  // §37.10 detail 3: an instance is a package, module, interface, or program.
  return type == kVpiModule || type == vpiPackage || type == vpiInterface ||
         type == vpiProgram;
}

VpiHandle VpiInstanceOf(VpiHandle obj) {
  // §37.10 detail 3: walk outward to the first enclosing scope that is itself
  // an instance; that is the immediate instance the object is instantiated in.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsInstanceType(scope->type)) return scope;
  }
  return nullptr;
}

VpiHandle VpiModuleOf(VpiHandle obj) {
  // §37.10 detail 2: report the nearest enclosing module, or null when no
  // module encloses the object.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (scope->type == kVpiModule) return scope;
  }
  return nullptr;
}

int VpiMemoryIterationItemType() {
  // §37.10 detail 4: the iteration yields array variable objects, never the
  // legacy vpiMemory object kind.
  return vpiRegArray;
}

std::string VpiCompilationUnitFullName(std::string_view object_path) {
  // §37.10 detail 5: such names begin with the "$unit::" scope name.
  return "$unit::" + std::string(object_path);
}

std::string VpiPackageFullName(std::string_view package_name) {
  // §37.10 detail 5: a package's full name is its own name ending in "::".
  return std::string(package_name) + "::";
}

std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path) {
  // §37.10 detail 5: package name, the "::" separator, then the member path.
  return std::string(package_name) + "::" + std::string(member_path);
}

std::string_view VpiNameSeparator(bool package_or_class_defn_boundary) {
  // §37.10 detail 5: "::" follows a package or class-definition scope; "." is
  // used in every other case.
  return package_or_class_defn_boundary ? "::" : ".";
}

bool VpiHandleByNameAccessible(const VpiObject& obj) {
  // §37.10 detail 6: imported items and compilation-unit objects are not
  // reachable through vpi_handle_by_name().
  return !obj.imported && !obj.in_compilation_unit;
}

int VpiSmallestTimePrecision(const std::vector<int>& precisions) {
  // §37.10 detail 7: the smallest (finest) precision wins; nothing to report
  // when the design has no modules.
  if (precisions.empty()) return 0;
  int smallest = precisions.front();
  for (int precision : precisions) {
    if (precision < smallest) smallest = precision;
  }
  return smallest;
}

}  // namespace delta
