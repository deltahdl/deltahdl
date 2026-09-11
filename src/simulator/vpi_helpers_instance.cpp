#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_specify.h"
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"

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

VpiHandle VpiScopeNamedClockingBlock(VpiHandle scope, bool global) {
  // §37.5/§37.6/§37.9 (figure): the clocking block a scope named default, or
  // the one it named global. §14.12 lets a scope name one of each among the
  // blocks it declares, so the block carries which it is and the edge reaches
  // the one so marked. Null where the scope named none.
  if (!scope) return nullptr;
  for (auto* child : scope->children) {
    if (child->type != vpiClockingBlock) continue;
    if (global ? child->global_clocking : child->default_clocking) return child;
  }
  return nullptr;
}

VpiHandle VpiScopeDefaultDisableIff(VpiHandle scope) {
  // §37.5/§37.6/§37.9 (figure): the vpiDefaultDisableIff edge is drawn to an
  // enclosure with no name holding an expr and a distribution, and §37.4.1
  // makes such an enclosure a grouping of the objects in it. So what the edge
  // reaches is an expression or a distribution; a scope names at most one, so
  // it is the first child of either kind. Null where the scope wrote none.
  if (!scope) return nullptr;
  for (auto* child : scope->children) {
    if (VpiIsExprType(child->type) || child->type == vpiDistribution) {
      return child;
    }
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

// ===========================================================================
// §37.36 UDP.
// ===========================================================================

std::vector<const UdpDecl*> VpiDesignUdpDecls(const RtlirDesign* design) {
  std::vector<const UdpDecl*> decls;
  if (design == nullptr) return decls;

  std::vector<const RtlirModule*> work(design->top_modules.begin(),
                                       design->top_modules.end());
  while (!work.empty()) {
    const RtlirModule* mod = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    for (const auto& child : mod->children) work.push_back(child.resolved);
    for (const RtlirUdpInst& inst : mod->udp_insts) {
      if (inst.decl == nullptr) continue;
      if (std::find(decls.begin(), decls.end(), inst.decl) == decls.end()) {
        decls.push_back(inst.decl);
      }
    }
  }
  return decls;
}

void VpiFillUdpDefnObject(VpiObject* obj, const UdpDecl& decl,
                          std::deque<std::string>& names) {
  obj->type = vpiUdpDefn;
  names.emplace_back(decl.name);
  obj->name = names.back();
  obj->def_name = std::string(decl.name);
  obj->size = static_cast<int>(decl.input_names.size());
  // §37.36 detail 2: "vpiPrimType returns vpiSeqPrim for sequential UDPs and
  // vpiCombPrim for combinational UDPs."
  obj->prim_type = decl.is_sequential ? vpiSeqPrim : vpiCombPrim;
}

void VpiFillUdpTableEntryObject(VpiObject* obj, const UdpTableRow& row,
                                VpiObject* defn) {
  obj->type = vpiTableEntry;
  // The symbol entries of a row are the input symbols it matches on, the
  // current state a sequential row carries, and the output symbol it names.
  obj->size = static_cast<int>(row.inputs.size()) +
              (row.current_state != 0 ? 1 : 0) + 1;
  obj->parent = defn;
  defn->children.push_back(obj);
}

}  // namespace delta
