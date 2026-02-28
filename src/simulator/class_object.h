#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

struct ClassDecl;
struct ClassMember;
struct ModuleItem;
class Arena;

// Forward declare for vtable entries.
struct ClassTypeInfo;

// §8.20: Virtual method table entry.
struct VTableEntry {
  std::string_view method_name;
  ModuleItem* method = nullptr;          // Resolved method body.
  const ClassTypeInfo* owner = nullptr;  // Class that defined this method.
};

// §8: Class type descriptor used for runtime type checking and dispatch.
struct ClassTypeInfo {
  std::string_view name;
  const ClassTypeInfo* parent = nullptr;
  const ClassDecl* decl = nullptr;
  bool is_abstract = false;

  // Property metadata (name -> default init value).
  struct PropertyInfo {
    std::string_view name;
    uint32_t width = 32;
    bool is_static = false;
  };
  std::vector<PropertyInfo> properties;

  // Non-virtual methods (including constructor).
  std::unordered_map<std::string, ModuleItem*> methods;

  // §8.20: Virtual method table (includes inherited virtuals).
  std::vector<VTableEntry> vtable;

  // §8.10: Static property storage (class-level, shared by all instances).
  std::unordered_map<std::string, Logic4Vec> static_properties;

  // Look up vtable index by method name; returns -1 if not found.
  int FindVTableIndex(std::string_view mname) const;

  // Check if this type is the same as or derived from `other`.
  bool IsA(const ClassTypeInfo* other) const;
};

// §8: Runtime class object instance (handle semantics, §8.12).
struct ClassObject {
  const ClassTypeInfo* type = nullptr;
  std::unordered_map<std::string, Logic4Vec> properties;

  // Get a property value, walking up inheritance chain defaults.
  Logic4Vec GetProperty(std::string_view name, Arena& arena) const;

  // Set a property value.
  void SetProperty(std::string_view name, const Logic4Vec& val);

  // §8.20: Dispatch a virtual method — walks vtable.
  ModuleItem* ResolveVirtualMethod(std::string_view name) const;

  // Resolve a non-virtual method (walk type chain).
  ModuleItem* ResolveMethod(std::string_view name) const;
};

// Sentinel value: null class handle is encoded as handle_id == 0.
inline constexpr uint64_t kNullClassHandle = 0;

}  // namespace delta
