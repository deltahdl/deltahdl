#pragma once

#include <cstdint>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

struct ClassDecl;
struct ClassMember;
struct Expr;
struct ModuleItem;
class Arena;

enum class Reachability {
  kStronglyReachable,
  kWeaklyReachable,
  kUnreachable,
};

struct ClassTypeInfo;

struct VTableEntry {
  std::string_view method_name;
  ModuleItem* method = nullptr;
  const ClassTypeInfo* owner = nullptr;
};

struct ClassTypeInfo {
  std::string_view name;
  const ClassTypeInfo* parent = nullptr;
  const ClassDecl* decl = nullptr;
  bool is_abstract = false;
  bool is_interface = false;
  std::vector<const ClassTypeInfo*> extended_interfaces;

  struct PropertyInfo {
    std::string_view name;
    uint32_t width = 32;
    bool is_static = false;
    bool is_local = false;
    bool is_protected = false;
    bool is_const = false;
    Expr* init_expr = nullptr;
  };
  std::vector<PropertyInfo> properties;

  std::unordered_map<std::string, ModuleItem*> methods;

  std::vector<VTableEntry> vtable;

  std::unordered_map<std::string, Logic4Vec> static_properties;

  std::unordered_map<std::string, uint64_t> enum_members;

  int FindVTableIndex(std::string_view mname) const;

  bool IsA(const ClassTypeInfo* other) const;
};

struct ClassObject {
  const ClassTypeInfo* type = nullptr;
  std::unordered_map<std::string, Logic4Vec> properties;
  uint32_t ref_count = 0;

  // §18.14.1 object stability: every instance owns an independent RNG for its
  // randomization methods. The allocating context installs rng_seed when the
  // object is created -- drawn from the creating thread's stream when one is
  // running, or from the enclosing initialization RNG for objects built by a
  // static declaration initializer (when no thread is active). The generator
  // is materialized lazily on first use so two objects created in the same
  // order from the same starting state always replay the same seeds.
  uint32_t rng_seed = 0;
  std::mt19937 rng;
  bool rng_initialized = false;

  Logic4Vec GetProperty(std::string_view name, Arena& arena) const;

  void SetProperty(std::string_view name, const Logic4Vec& val);

  ModuleItem* ResolveVirtualMethod(std::string_view name) const;

  ModuleItem* ResolveMethod(std::string_view name) const;

  ModuleItem* ResolveMethodForType(std::string_view name,
                                   const ClassTypeInfo* from_type) const;

  Logic4Vec GetPropertyForType(std::string_view name,
                               const ClassTypeInfo* declared_type,
                               Arena& arena) const;

  void SetPropertyForType(std::string_view name,
                          const ClassTypeInfo* declared_type,
                          const Logic4Vec& val);

  ClassObject* ShallowCopy(Arena& arena) const;
};

inline constexpr uint64_t kNullClassHandle = 0;

struct WeakReference {
  uint64_t referent_handle = kNullClassHandle;

  uint64_t Get() const { return referent_handle; }

  void Clear() { referent_handle = kNullClassHandle; }

  static int64_t GetId(uint64_t obj_handle) {
    return (obj_handle == kNullClassHandle) ? 0
                                            : static_cast<int64_t>(obj_handle);
  }
};

}
