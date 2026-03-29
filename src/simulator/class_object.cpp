#include "simulator/class_object.h"

#include "common/arena.h"
#include "parser/ast.h"

namespace delta {

// --- ClassTypeInfo ---

int ClassTypeInfo::FindVTableIndex(std::string_view mname) const {
  for (size_t i = 0; i < vtable.size(); ++i) {
    if (vtable[i].method_name == mname) return static_cast<int>(i);
  }
  return -1;
}

bool ClassTypeInfo::IsA(const ClassTypeInfo* other) const {
  for (const auto* cur = this; cur != nullptr; cur = cur->parent) {
    if (cur == other) return true;
  }
  return false;
}

// --- ClassObject ---

Logic4Vec ClassObject::GetProperty(std::string_view name, Arena& arena) const {
  std::string key(name);
  auto it = properties.find(key);
  if (it != properties.end()) return it->second;
  if (type) {
    auto sit = type->static_properties.find(key);
    if (sit != type->static_properties.end()) return sit->second;
  }
  return MakeLogic4VecVal(arena, 32, 0);
}

void ClassObject::SetProperty(std::string_view name, const Logic4Vec& val) {
  std::string key(name);
  if (type) {
    auto it = type->static_properties.find(key);
    if (it != type->static_properties.end()) {
      it->second = val;
      return;
    }
  }
  properties[key] = val;
}

ModuleItem* ClassObject::ResolveVirtualMethod(std::string_view name) const {
  if (!type) return nullptr;
  int idx = type->FindVTableIndex(name);
  if (idx >= 0) return type->vtable[static_cast<size_t>(idx)].method;
  return nullptr;
}

ModuleItem* ClassObject::ResolveMethod(std::string_view name) const {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(name));
    if (it != t->methods.end()) return it->second;
  }
  return nullptr;
}

ModuleItem* ClassObject::ResolveMethodForType(
    std::string_view name, const ClassTypeInfo* from_type) const {
  for (const auto* t = from_type; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(name));
    if (it != t->methods.end()) return it->second;
  }
  return nullptr;
}

Logic4Vec ClassObject::GetPropertyForType(std::string_view name,
                                          const ClassTypeInfo* declared_type,
                                          Arena& arena) const {
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) return it->second;
  }
  return GetProperty(name, arena);
}

void ClassObject::SetPropertyForType(std::string_view name,
                                     const ClassTypeInfo* declared_type,
                                     const Logic4Vec& val) {
  for (const auto* t = declared_type; t != nullptr; t = t->parent) {
    std::string scoped = std::string(t->name) + "::" + std::string(name);
    auto it = properties.find(scoped);
    if (it != properties.end()) {
      it->second = val;
      // Keep the bare key in sync when writing through the most-derived type.
      if (declared_type == type)
        properties[std::string(name)] = val;
      return;
    }
  }
  SetProperty(name, val);
}

ClassObject* ClassObject::ShallowCopy(Arena& arena) const {
  auto* copy = arena.Create<ClassObject>();
  copy->type = type;
  copy->properties = properties;
  return copy;
}

}  // namespace delta
