#include "simulator/vpi_design_prefixed_refs.h"

#include <algorithm>
#include <functional>
#include <string>
#include <string_view>

#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

const ModuleDecl* VpiVirtualInterfaceOf(const RtlirDesign& design,
                                        const DataType* type,
                                        const RtlirModule* mod) {
  if (type == nullptr) return nullptr;
  std::string_view interface_name = type->type_name;
  if (type->kind == DataTypeKind::kNamed) {
    const auto kTypedef = design.type_interfaces.find(NamedTypeKey(*type));
    if (kTypedef == design.type_interfaces.end()) return nullptr;
    interface_name = kTypedef->second;
  } else if (type->kind != DataTypeKind::kVirtualInterface) {
    return nullptr;
  }
  return &VpiElementDeclFrom(mod == nullptr ? nullptr : mod->decl,
                             *design.compilation_unit, interface_name);
}

bool VpiIsDynamicPrefixHolderType(int type) {
  return type == vpiClassVar || type == vpiVirtualInterfaceVar ||
         type == vpiClockingBlock;
}

namespace {

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
  const ModuleDecl* iface = holder->decl_facts.vif_interface;
  if (iface == nullptr) return nullptr;
  const std::string_view kMember = written.substr(written.find('.') + 1);
  if (std::ranges::none_of(iface->items, [kMember](const ModuleItem* declared) {
        return declared->kind == ModuleItemKind::kClockingBlock &&
               declared->name == kMember;
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

VpiObject* HeldInstance(
    std::string_view scope,
    const std::function<VpiObject*(const std::string&)>& by_name) {
  return scope.empty() ? nullptr : by_name(std::string(scope));
}

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
