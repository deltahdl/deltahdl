#include <algorithm>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

void VpiMakePortBits(VpiObject* port, const VpiAttachBuild& build) {
  if (port->low_conn == nullptr) return;
  for (VpiObject* bit : port->low_conn->children) {
    if (!VpiIsBitObjectType(bit->type)) continue;
    VpiObject* port_bit = build.alloc();
    port_bit->type = vpiPortBit;
    port_bit->parent = port;
    port_bit->direction = port->direction;
    port_bit->size = 1;
    port_bit->index = bit->index;
    port_bit->index_expr = VpiIntConstant(bit->index, build);
    port_bit->bit_offset = bit->bit_offset;
    port_bit->low_conn = bit;
    port->children.push_back(port_bit);
  }
}

namespace {

VpiObject* PortNamed(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == kVpiPort && child->name == name) return child;
  }
  return nullptr;
}

VpiObject* PortRefObj(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == vpiIODecl && child->name == name &&
        child->io_expr != nullptr && child->io_expr->type == vpiRefObj) {
      return child->io_expr;
    }
  }
  return nullptr;
}

void ConnectLowConns(VpiHandle module, const std::string& instance,
                     const VpiObjectMap& objects, const VpiAttachBuild& build) {
  for (VpiObject* port : module->children) {
    if (port->type != kVpiPort || port->low_conn != nullptr ||
        port->name.empty()) {
      continue;
    }
    port->low_conn =
        FindObjectForFlatName(objects, VpiFlatName(instance, port->name));
    VpiMakePortBits(port, build);
    VpiObject* ref_obj = PortRefObj(module, port->name);
    if (ref_obj != nullptr) port->low_conn = ref_obj;
    if (port->direction == vpiInput) {
      VpiHangOnVariablesNamed(port, port->low_conn);
    }
  }
}

VpiObject* ModportNamed(VpiHandle target, std::string_view name) {
  if (target == nullptr) return nullptr;
  VpiHandle iface = target->type == vpiModport ? target->parent : target;
  const auto kFound =
      std::ranges::find_if(iface->children, [&](VpiHandle child) {
        return child->type == vpiModport && child->name == name;
      });
  return kFound == iface->children.end() ? nullptr : *kFound;
}

VpiObject* MakeRefObj(std::string_view name, std::string full_name,
                      VpiObject* parent, VpiObject* actual,
                      const VpiAttachBuild& build) {
  VpiObject* ref_obj = build.alloc();
  ref_obj->type = vpiRefObj;
  ref_obj->name = build.keep(std::string(name));
  ref_obj->full_name = std::move(full_name);
  ref_obj->parent = parent;
  ref_obj->actual = actual;
  return ref_obj;
}

struct ConnectionSite {
  VpiHandle writer;
  const VpiExprNames& names;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

std::string InstanceNameOf(const Expr* head) {
  if (head->kind == ExprKind::kIdentifier) return std::string(head->text);
  const bool kElement = head->kind == ExprKind::kSelect &&
                        head->base->kind == ExprKind::kIdentifier &&
                        head->index->kind == ExprKind::kIntegerLiteral &&
                        head->index_end == nullptr;
  return kElement ? std::string(head->base->text) + "[" +
                        std::to_string(head->index->int_val) + "]"
                  : std::string();
}

VpiObject* InterfaceHighConn(const Expr* conn, const ConnectionSite& site) {
  const bool kSelects = conn->kind == ExprKind::kMemberAccess;
  const Expr* head = kSelects ? conn->lhs : conn;
  const std::string kName = InstanceNameOf(head);
  if (kName.empty()) return nullptr;
  VpiObject* base = PortRefObj(site.writer, kName);
  if (base == nullptr) {
    VpiObject* instance =
        head->kind == ExprKind::kIdentifier
            ? VpiGenBlockExpression(head, site.names, site.ctx, site.build)
            : nullptr;
    if (instance == nullptr) {
      instance = FindObjectForFlatName(site.names.objects,
                                       VpiFlatName(site.names.prefix, kName));
    }
    if (instance == nullptr) {
      instance = FindObjectForFlatName(site.names.objects, kName);
    }
    base = MakeRefObj(kName, VpiScopedFullName(site.writer, kName), site.writer,
                      instance, site.build);
  }
  if (!kSelects) return base;
  const std::string_view kMember = conn->rhs->text;
  VpiObject* modport = ModportNamed(base->actual, kMember);
  if (modport == nullptr) return nullptr;
  return MakeRefObj(kName + "." + std::string(kMember),
                    base->full_name + "." + std::string(kMember), base, modport,
                    site.build);
}

void BindPortRefObj(VpiHandle module, const RtlirPort& port, VpiHandle high) {
  VpiObject* ref_obj = PortRefObj(module, port.name);
  const std::string_view kModport = port.declared_type->modport_name;
  ref_obj->actual =
      kModport.empty() ? high->actual : ModportNamed(high->actual, kModport);
  ref_obj->generic_interface = port.interface_type_name.empty();
}

VpiObject* HighConnOf(const RtlirModuleInst& inst,
                      const RtlirPortBinding& binding, VpiObject* port,
                      const ConnectionSite& site) {
  const RtlirPort& declared = *std::ranges::find(
      inst.resolved->ports, binding.port_name, &RtlirPort::name);
  VpiObject* high = declared.is_interface_port
                        ? InterfaceHighConn(binding.connection, site)
                        : nullptr;
  if (high != nullptr) {
    BindPortRefObj(port->parent, declared, high);
    return high;
  }
  high = VpiGenBlockExpression(binding.connection, site.names, site.ctx,
                               site.build);
  VpiObject* ref_obj = declared.direction == Direction::kRef
                           ? PortRefObj(port->parent, declared.name)
                           : nullptr;
  if (ref_obj != nullptr) ref_obj->actual = high;
  return high;
}

void ConnectPorts(const RtlirModuleInst& inst, VpiHandle writer,
                  const VpiExprNames& names, SimContext& ctx,
                  const VpiAttachBuild& build) {
  const VpiObjectMap& objects = names.objects;
  const std::string kInstance = VpiFlatName(names.prefix, inst.inst_name);
  VpiHandle module = VpiChildInstanceObject(objects, writer, kInstance, inst);
  if (module == nullptr) return;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    VpiObject* port = PortNamed(module, binding.port_name);
    if (port == nullptr) continue;
    port->high_conn =
        binding.unconnected
            ? nullptr
            : HighConnOf(inst, binding, port, {writer, names, ctx, build});
    port->conn_by_name = inst.ports_by_name && !binding.unconnected;
    if (VpiPortIsComplexExpressionLoad(port)) {
      VpiHangOnNetsNamed(port, port->high_conn);
    }
    if (port->direction == vpiOutput) {
      VpiHangOnVariablesNamed(port, port->high_conn);
    }
  }
  ConnectLowConns(module, kInstance, objects, build);
}

}  // namespace

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        if (instance->top_module) {
          ConnectLowConns(instance, prefix, objects, build);
        }
        for (const RtlirModuleInst& inst : mod->children) {
          const VpiCallStand kStand{
              VpiGenScopeOf(instance, inst.gen_block_path), mod};
          ConnectPorts(inst, instance,
                       {objects, prefix, inst.gen_block_prefixes, nullptr,
                        &mod->node_attrs, &kStand, mod, instance},
                       ctx, build);
        }
      });
}

}  // namespace delta
