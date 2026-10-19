#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
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

// The port object `module` holds under `name`, null for none.
VpiObject* PortNamed(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == kVpiPort && child->name == name) return child;
  }
  return nullptr;
}

// §37.15 detail 1: the ref obj the io decl `module` holds for its ref,
// interface or modport port `name`, null for a port of any other kind.
VpiObject* PortRefObj(VpiHandle module, std::string_view name) {
  for (VpiObject* child : module->children) {
    if (child->type == vpiIODecl && child->name == name &&
        child->io_expr != nullptr && child->io_expr->type == vpiRefObj) {
      return child->io_expr;
    }
  }
  return nullptr;
}

// §37.14 with §37.15 detail 1: the lower connection of each port of
// `module`, the instance keyed under `instance`, is the instance's own net or
// variable of the port's name, or the ref obj its io decl holds for a ref,
// interface or modport port (§37.14 detail 5).
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
    // The port bits stay those of the instance's own net or variable.
    VpiObject* ref_obj = PortRefObj(module, port->name);
    if (ref_obj != nullptr) port->low_conn = ref_obj;
  }
}

// The modport named `name` of `target`, an interface or one of its modports;
// null for none.
VpiObject* ModportNamed(VpiHandle target, std::string_view name) {
  if (target == nullptr) return nullptr;
  VpiHandle iface = target->type == vpiModport ? target->parent : target;
  const auto kFound =
      std::ranges::find_if(iface->children, [&](VpiHandle child) {
        return child->type == vpiModport && child->name == name;
      });
  return kFound == iface->children.end() ? nullptr : *kFound;
}

// A ref obj named `name` and `full_name`, held by `parent` and bound to
// `actual`.
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

// Where a connection is written: the instance `writer` holding the
// instantiation, the names its expressions resolve by, and what a run builds
// with.
struct ConnectionSite {
  VpiHandle writer;
  const VpiExprNames& names;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// The name the interface instance `head` writes is keyed under: its
// identifier, or an element of an array of interface instances, `ia[1]`, by
// the array's name and the element's index, as the elaborator names it
// (§23.3.2); empty for any other expression.
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

// §37.15 detail 2 and its example: the higher connection `conn` of an
// interface or modport port, written at `site`, is a
// ref obj. Where it names an interface port of the writer, `s`, it is a use of
// that port's ref obj; where it names an interface instance, `i`, or an
// element of an array of them, `ia[1]`, a ref obj bound to that instance; and
// where it selects a modport of either, `s.initiator`, a ref obj bound to the
// modport that is a subelement of the first (detail 4). §23.6: an instance
// named by a path the elaborator keeps whole, `top.i` written in a module
// below top, is found by that path from the design's root once the writer's
// scope reaches nothing by it. Null for a connection of any other shape or
// that selects no modport, each left the expression it is.
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

// §37.15 example: the ref obj of the interface or modport port `port` of
// `module`, whose higher connection is the ref obj `high`, is bound to what
// `high` is, or to the modport of it the port's declaration selects. A port
// declared with the `interface` keyword names no interface of its own, which
// makes it a reference to a generic interface (§25.3.3, detail 5).
void BindPortRefObj(VpiHandle module, const RtlirPort& port, VpiHandle high) {
  VpiObject* ref_obj = PortRefObj(module, port.name);
  const std::string_view kModport = port.declared_type->modport_name;
  ref_obj->actual =
      kModport.empty() ? high->actual : ModportNamed(high->actual, kModport);
  ref_obj->generic_interface = port.interface_type_name.empty();
}

// §37.14 detail 3 with §37.15: the higher connection of `port`, the port
// `binding` connects in `inst`, written at `site`. For an interface or
// modport port whose connection is one it is a ref obj (InterfaceHighConn),
// through which the port's own ref obj is bound; otherwise it is the
// expression the instantiation wrote, which a ref port's ref obj is bound to,
// as D4's example binds r to a.
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

// §37.14 details 3, 4 and 10: the ports of the instance `inst` connected -
// each port's higher connection the expression the instantiation wrote for
// it, its names resolved as `names` says, in the generate blocks and the
// instance `writer` holding the instantiation, or a ref obj for an interface
// or modport port (§37.15), and its lower connection the instance's own net or
// variable of the port's name or its ref obj. A port the instantiation leaves
// unconnected reaches no higher connection, though the elaborator supplies its
// default, a pull or 'z in its place. A port a named list connects, .a(w) or
// .*, is connected by name (§37.14).
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
    // §37.46 detail 1: a port a complex expression connects loads the nets
    // the expression reads.
    if (VpiPortIsComplexExpressionLoad(port)) {
      VpiHangOnNetsNamed(port, port->high_conn);
    }
  }
  ConnectLowConns(module, kInstance, objects, build);
}

// The elements of `holder`, one per index of `dims[depth]` in the order it
// declares them, each an interconnect array of the dimensions after it or, of
// the last, an interconnect net.
void FillInterconnectLevel(VpiObject* holder,
                           const std::vector<RtlirUnpackedDim>& dims,
                           std::size_t depth,
                           const std::function<VpiObject*()>& alloc,
                           std::deque<std::string>& names) {
  const RtlirUnpackedDim& dim = dims[depth];
  const bool kLast = depth + 1 == dims.size();
  holder->size = static_cast<int>(dim.Size());
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  for (int64_t index = dim.left;; index += kStep) {
    VpiObject* element = alloc();
    element->type = kLast ? vpiInterconnectNet : vpiInterconnectArray;
    names.push_back(std::string(holder->name) + "[" + std::to_string(index) +
                    "]");
    element->name = names.back();
    element->parent = holder;
    element->index = static_cast<int>(index);
    element->array_member = true;
    holder->children.push_back(element);
    if (!kLast) FillInterconnectLevel(element, dims, depth + 1, alloc, names);
    if (index == dim.right) break;
  }
}

}  // namespace

void VpiMakeInterconnectArray(VpiObject* net, const RtlirPort& port,
                              const std::function<VpiObject*()>& alloc,
                              std::deque<std::string>& names) {
  if (port.unpacked_dims.empty()) return;
  net->type = vpiInterconnectArray;
  FillInterconnectLevel(net, port.unpacked_dims, 0, alloc, names);
}

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build) {
  // §37.14: a port reaches through vpiHighConn the connection the
  // instantiation makes to it and through vpiLowConn the one inside the
  // instance. Neither was linked but an interconnect port's lower one, so both
  // relations were null for every port of every design. A vector port holds a
  // port bit per bit, which no design had either.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        // §37.5: a top module's ports have a lower connection and, with no
        // instantiation over them, no higher one.
        if (instance->top_module) {
          ConnectLowConns(instance, prefix, objects, build);
        }
        for (const RtlirModuleInst& inst : mod->children) {
          // §37.42: a call a connection makes stands in the instance writing
          // it, or in the gen scope the instantiation stands in (§37.85).
          const VpiCallStand kStand{
              VpiGenScopeOf(instance, inst.gen_block_path), mod};
          ConnectPorts(inst, instance,
                       {objects, prefix, inst.gen_block_prefixes, nullptr,
                        &mod->node_attrs, &kStand},
                       ctx, build);
        }
      });
}

}  // namespace delta
