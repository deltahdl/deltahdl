#include "simulator/vpi_design_prefixed_refs.h"

#include <algorithm>
#include <cstddef>
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
  const std::size_t kDot = written.find('.');
  if (holder->type != vpiVirtualInterfaceVar || iface == nullptr ||
      kDot == std::string_view::npos) {
    return nullptr;
  }
  const std::string_view kMember = written.substr(kDot + 1);
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

// The clocking block `block`, which a virtual interface var prefixes, stands
// for now in the run `ctx` (VpiRefreshPrefixedClockingBlock).
VpiObject* PrefixedClockingBlockActual(
    const VpiObject& block, SimContext& ctx,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  Variable* vif = block.prefix->var;
  if (vif == nullptr || !ctx.VirtualInterfaceIsBound(vif)) return nullptr;
  const VpiObject* instance =
      by_name(std::string(ctx.VirtualInterfaceBinding(vif)));
  if (instance == nullptr) return nullptr;
  const std::string_view kMember = block.name.substr(block.name.rfind('.') + 1);
  for (VpiObject* child : instance->children) {
    if (child->type == vpiClockingBlock && child->name == kMember) return child;
  }
  return nullptr;
}

}  // namespace

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
