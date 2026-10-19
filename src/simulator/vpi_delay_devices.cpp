#include "simulator/vpi_delay_devices.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The device a delay term on `net` belongs to whose delay `source` holds, or
// null where `source` has placed none there yet.
VpiObject* FindDelayDevice(const VpiObject* source, const VpiObject* net) {
  for (const VpiObject* child : net->children) {
    if (child->type != vpiDelayTerm || child->parent == nullptr) continue;
    if (child->parent->delay_source == source) return child->parent;
  }
  return nullptr;
}

// §37.45: one of a device's two terms. It reports the device's vpiDelayType,
// reaches the device through vpiDelayDevice, and sits on the device's net.
VpiObject* MakeDelayTerm(VpiObject* device, VpiObject* net,
                         const std::function<VpiObject*()>& alloc) {
  VpiObject* term = alloc();
  term->type = vpiDelayTerm;
  term->delay_type = device->delay_type;
  term->parent = device;
  term->term_net = net;
  net->children.push_back(term);
  return term;
}

// §32.4.4: the port an SDF interconnect entry names by `name`, its cell's
// instance prefix in front and either hierarchy divider between the parts
// (§32.4.1): the port of the instance the path ahead of the last divider
// names, called what follows it, a select written after it read as the whole
// port. Null where the name reaches no such port, a signal of a module's own
// scope among them.
VpiObject* SdfPortObject(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    std::string_view name) {
  std::string flat(name.substr(0, name.find('[')));
  std::ranges::replace(flat, '/', '.');
  const std::size_t kDot = flat.rfind('.');
  if (kDot == std::string::npos) return nullptr;
  const std::string_view kFlat(flat);
  VpiObject* instance = FindObjectForFlatName(objects, kFlat.substr(0, kDot));
  if (instance == nullptr) return nullptr;
  const std::string_view kPort = kFlat.substr(kDot + 1);
  auto found =
      std::ranges::find_if(instance->children, [kPort](const VpiObject* c) {
        return c->type == vpiPort && c->name == kPort;
      });
  return found == instance->children.end() ? nullptr : *found;
}

// §37.37: the intermodule path running from the port `from` to the port `to`,
// null where the design connects no such path.
VpiObject* InterModPathBetween(const VpiObject* from, const VpiObject* to) {
  if (from == nullptr) return nullptr;
  auto found =
      std::ranges::find_if(from->children, [from, to](const VpiObject* c) {
        return c->type == vpiInterModPath && c->children.size() == 2 &&
               c->children[0] == from && c->children[1] == to;
      });
  return found == from->children.end() ? nullptr : *found;
}

}  // namespace

VpiObject* VpiPlaceDelayDevice(VpiObject* source, VpiObject* net,
                               VpiObject* module, int delay_type,
                               const std::function<VpiObject*()>& alloc) {
  if (source == nullptr || net == nullptr) return nullptr;
  if (VpiObject* found = FindDelayDevice(source, net)) return found;

  VpiObject* device = alloc();
  device->type = vpiDelayDevice;
  device->delay_type = delay_type;
  device->delay_source = source;
  // §37.45 draws the edge between the device and its module from the device
  // alone, and §37.5 gives a module no vpiDelayDevice relation, so the device
  // reaches its module without the module holding it among its children.
  device->parent = module;
  device->in_term = MakeDelayTerm(device, net, alloc);
  device->out_term = MakeDelayTerm(device, net, alloc);
  return device;
}

VpiObject* VpiPlaceInterModPathDevice(
    VpiObject* path, const std::function<VpiObject*()>& alloc) {
  if (path->children.empty()) return nullptr;
  VpiObject* net = path->children.front()->high_conn;
  if (net == nullptr || !VpiIsNetsType(net->type)) return nullptr;
  return VpiPlaceDelayDevice(path, net, net->parent, vpiInterModPathDelay,
                             alloc);
}

VpiObject* VpiDelayTermValueNet(const VpiObject& term) {
  const VpiObject& device = *term.parent;
  if (device.out_term != &term || device.delay_type != vpiModPathDelay) {
    return term.term_net;
  }
  for (VpiObject* child : device.parent->children) {
    if (child->type != vpiPort || child->name != term.term_net->name) continue;
    VpiObject* high = child->high_conn;
    if (high != nullptr && VpiIsNetsType(high->type)) return high;
  }
  return term.term_net;
}

void VpiContext::PlaceSdfDelayDevice(std::string_view source,
                                     std::string_view load) {
  VpiObject* load_port = SdfPortObject(object_map_, load);
  if (load_port == nullptr) return;
  const auto kAlloc = [this] { return AllocObject(); };
  if (source.empty()) {
    // §32.4.4: a PORT entry gives the port a module input port delay, which
    // sits on the net the port's lower connection names inside its instance.
    VpiObject* net = load_port->low_conn;
    if (net != nullptr && VpiIsNetsType(net->type)) {
      VpiPlaceDelayDevice(load_port, net, load_port->parent, vpiMIPDelay,
                          kAlloc);
    }
    return;
  }
  // §32.4.4: an INTERCONNECT entry gives the intermodule path between its two
  // ports a delay.
  if (VpiObject* path =
          InterModPathBetween(SdfPortObject(object_map_, source), load_port)) {
    VpiPlaceInterModPathDevice(path, kAlloc);
  }
}

}  // namespace delta
