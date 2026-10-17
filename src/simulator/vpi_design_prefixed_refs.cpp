#include <functional>
#include <string>
#include <string_view>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

bool VpiIsDynamicPrefixHolderType(int type) {
  return type == vpiClassVar || type == vpiVirtualInterfaceVar ||
         type == vpiClockingBlock;
}

VpiObject* VpiClockingBlockAround(const VpiObject* scope,
                                  const VpiObjectMap& objects,
                                  const std::string& instance,
                                  std::string_view name) {
  // §14.3: a clocking block is a scope of the instance rather than a name in
  // it, found from the blocks around the expression out to the instance.
  if (scope == nullptr) {
    const auto kAt = objects.find(instance);
    if (kAt != objects.end()) scope = kAt->second;
  }
  for (const VpiObject* at = scope; at != nullptr; at = at->parent) {
    for (VpiObject* child : at->children) {
      if (child->type == vpiClockingBlock && child->name == name) return child;
    }
  }
  return nullptr;
}

VpiObject* VpiPrefixedReference(VpiObject* holder, std::string_view written,
                                const std::function<VpiObject*()>& alloc,
                                const VpiNameKeeper& keep) {
  VpiObject* ref = alloc();
  ref->type = vpiRefObj;
  ref->name = keep(std::string(written));
  ref->prefix = holder;
  return ref;
}

}  // namespace delta
