#include "simulation/class_object.h"

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
  return MakeLogic4VecVal(arena, 32, 0);
}

void ClassObject::SetProperty(std::string_view name, const Logic4Vec& val) {
  properties[std::string(name)] = val;
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

}  // namespace delta
