#include "simulator/virtual_interface.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §8.10: a static property is the class's own, read from the class that
// declares it whichever class the running method belongs to.
static uint64_t StaticPropertyHandle(const ClassTypeInfo* scope,
                                     std::string_view name) {
  for (const auto* t = scope; t != nullptr; t = t->parent) {
    auto it = t->static_properties.find(std::string(name));
    if (it != t->static_properties.end()) return it->second.ToUint64();
  }
  return kNullVirtualInterface;
}

// §8.15: an instance property is read against the class the running method is
// defined in, so a base method reads the base declaration even where a derived
// class shadows the name, as EvalIdentifierClassScope in evaluation.cpp reads
// any other property by its bare name.
static uint64_t InstancePropertyHandle(const ClassObject* self,
                                       const ClassTypeInfo* method_cls,
                                       std::string_view name, Arena& arena) {
  if (self == nullptr) return kNullVirtualInterface;
  Logic4Vec held = method_cls != nullptr
                       ? self->GetPropertyForType(name, method_cls, arena)
                       : self->GetProperty(name, arena);
  return held.ToUint64();
}

VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  VirtualInterfaceBase base;
  if (const Variable* var = ctx.FindVariable(name); var != nullptr) {
    base.is_virtual_interface = var->is_virtual_interface;
    if (base.is_virtual_interface) base.handle = var->value.ToUint64();
    return base;
  }
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* scope = method_cls != nullptr ? method_cls
                               : self != nullptr     ? self->type
                                                     : nullptr;
  if (scope == nullptr) return base;
  const ClassTypeInfo::PropertyInfo* prop = scope->FindProperty(name);
  if (prop == nullptr || !prop->is_virtual_interface) return base;
  base.is_virtual_interface = true;
  base.handle = prop->is_static
                    ? StaticPropertyHandle(scope, name)
                    : InstancePropertyHandle(self, method_cls, name, arena);
  return base;
}

std::string VirtualInterfaceComponentName(uint64_t handle,
                                          std::string_view field,
                                          const SimContext& ctx) {
  std::string_view scope = ctx.VirtualInterfaceScope(handle);
  if (scope.empty()) return {};
  std::string name(scope);
  name += ".";
  name += field;
  return name;
}

}  // namespace delta
