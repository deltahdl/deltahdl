#include "simulator/vpi_design_prefixed_refs.h"

#include <algorithm>
#include <functional>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

bool VpiIsDynamicPrefixHolderType(int type) {
  return type == vpiClassVar || type == vpiVirtualInterfaceVar ||
         type == vpiClockingBlock;
}

namespace {

// The clocking block named `name` that `from`, or a scope around it, declares.
VpiObject* ClockingBlockOutFrom(const VpiObject* from, std::string_view name) {
  for (const VpiObject* at = from; at != nullptr; at = at->parent) {
    for (VpiObject* child : at->children) {
      if (child->type == vpiClockingBlock && child->name == name) return child;
    }
  }
  return nullptr;
}

}  // namespace

const VpiObject* VpiScopeOrInstance(const VpiObject* scope,
                                    const VpiObjectMap& objects,
                                    const std::string& instance) {
  if (scope != nullptr) return scope;
  const auto kAt = objects.find(instance);
  return kAt != objects.end() ? kAt->second : nullptr;
}

VpiObject* VpiClockingBlockAround(const VpiObject* scope,
                                  const VpiObjectMap& objects,
                                  const std::string& instance,
                                  std::string_view name) {
  // §14.3: a clocking block is a scope of the instance rather than a name in
  // it, found from the blocks around the expression out to the instance, and
  // in the instance itself where those blocks are not yet hung from it.
  if (VpiObject* block = ClockingBlockOutFrom(scope, name)) return block;
  return ClockingBlockOutFrom(VpiScopeOrInstance(nullptr, objects, instance),
                              name);
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

VpiObject* VpiVirtualInterfaceClockingBlock(
    VpiObject* holder, std::string_view written,
    const std::function<VpiObject*()>& alloc, const VpiNameKeeper& keep) {
  const RtlirModule* iface = holder->decl_facts.vif_interface;
  if (holder->type != vpiVirtualInterfaceVar || iface == nullptr) {
    return nullptr;
  }
  const std::string_view kMember = written.substr(written.find('.') + 1);
  if (std::ranges::none_of(iface->clocking_blocks,
                           [kMember](const ModuleItem* declared) {
                             return declared->name == kMember;
                           })) {
    return nullptr;
  }
  VpiObject* block = alloc();
  block->type = vpiClockingBlock;
  block->name = keep(std::string(written));
  block->prefix = holder;
  return block;
}

namespace {

// §25.9: the interface instance a virtual interface holding the scope `scope`
// refers to, found by that name through `by_name`; null for the empty scope
// of one holding none.
VpiObject* HeldInstance(
    std::string_view scope,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  return scope.empty() ? nullptr : by_name(std::string(scope));
}

// The clocking block `block`, which a virtual interface var prefixes, stands
// for now in the run `ctx` (VpiRefreshPrefixedClockingBlock): the clocking
// block of its name the instance the var holds declares, and null while the
// var holds none. The block is looked for by its kind as well as its name,
// since the instance also holds the event variable §14.10 has the run name
// after it. The instance declares it, the var's interface having been found
// to (VpiVirtualInterfaceClockingBlock), so the walk out from the instance
// ends there.
VpiObject* PrefixedClockingBlockActual(
    const VpiObject& block, SimContext& ctx,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  return ClockingBlockOutFrom(
      HeldInstance(ctx.VirtualInterfaceBinding(block.prefix->var), by_name),
      block.name.substr(block.name.rfind('.') + 1));
}

}  // namespace

void VpiRefreshVirtualInterfaceActual(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  if (type != vpiActual || ref.type != vpiVirtualInterfaceVar ||
      ref.var == nullptr || ctx == nullptr) {
    return;
  }
  ref.actual = HeldInstance(
      ctx->VirtualInterfaceScope(ref.var->value.ToUint64()), by_name);
}

void VpiRefreshPrefixedClockingBlock(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  if (type != vpiActual || ref.type != vpiClockingBlock ||
      ref.prefix == nullptr || ctx == nullptr) {
    return;
  }
  ref.actual = PrefixedClockingBlockActual(ref, *ctx, by_name);
}

}  // namespace delta
