#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <deque>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
// §37.44's vpiThread is defined in the SystemVerilog VPI header.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"

namespace delta {

VpiHandle VpiContext::DesignScopeChild(VpiHandle parent, std::string_view part,
                                       std::string_view full_path) {
  if (parent == nullptr) {
    auto it = object_map_.find(part);
    if (it != object_map_.end()) return it->second;
  } else {
    for (auto* child : parent->children) {
      if (child->name == part) return child;
    }
  }

  // The component names an instance the walk has not been through before, so
  // the scope it stands for is made here. A leaf is made the same way and then
  // told what it is by the caller, because what distinguishes the two is the
  // design object hanging off the name rather than anything in the name.
  name_pool_.emplace_back(part);
  auto* obj = AllocObject();
  obj->type = kVpiModule;
  obj->name = name_pool_.back();
  obj->full_name = std::string(full_path);
  obj->parent = parent;
  if (parent == nullptr) {
    object_map_[obj->name] = obj;
  } else {
    obj->index = static_cast<int>(parent->children.size());
    parent->children.push_back(obj);
  }
  return obj;
}

VpiHandle VpiContext::DesignObjectForFlatName(std::string_view flat_name) {
  std::vector<std::string_view> parts = VpiNamePathComponents(flat_name);
  if (parts.empty()) return nullptr;

  VpiHandle current = nullptr;
  std::size_t consumed = 0;
  for (std::string_view part : parts) {
    consumed += part.size();
    current = DesignScopeChild(current, part, flat_name.substr(0, consumed));
    consumed += 1;  // the separator this component was followed by
  }
  return current;
}

VpiHandle VpiContext::ThreadObjectFor(Process* proc) {
  if (proc == nullptr) return nullptr;
  auto it = thread_objects_.find(proc);
  if (it != thread_objects_.end()) {
    // §37.44 (vpiActive): the property belongs to the process, so it is read
    // when asked for rather than frozen into the object when it was made.
    it->second->active = proc->active;
    return it->second;
  }
  auto* obj = AllocObject();
  obj->type = vpiThread;
  obj->active = proc->active;
  thread_objects_[proc] = obj;
  return obj;
}

void VpiContext::RefreshThreadObjects() {
  if (sim_ctx_ == nullptr) return;
  for (Process* proc : sim_ctx_->GetScheduler().Threads()) {
    VpiHandle obj = ThreadObjectFor(proc);
    // §37.44 (thread one-to-many thread): the threads this one spawned, which
    // detail 1 calls "a branch of a fork construct". They hang off the parent
    // as its thread children, which is where VpiThreadThreads reads them and
    // where VpiThreadParent reads the link back.
    for (Process* child : proc->children) {
      VpiHandle child_obj = ThreadObjectFor(child);
      if (child_obj->parent != nullptr) continue;
      child_obj->parent = obj;
      obj->children.push_back(child_obj);
    }
  }
}

namespace {

// The first child of `obj` whose type is `type`, which is how this model links
// a frame to the frames and threads around it.
VpiObject* FirstChildOfType(VpiObject* obj, int type) {
  if (obj == nullptr) return nullptr;
  for (auto* child : obj->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiContext::ActivateFrame() {
  // §36.6: a run holding no PLI application has no design attached and nothing
  // to reach a frame through, so it pays nothing for this.
  if (sim_ctx_ == nullptr) return nullptr;

  VpiHandle outer = active_frame_;
  VpiHandle thread = ThreadObjectFor(sim_ctx_->CurrentProcess());
  // §37.43 detail 5: "The vpiParent relation shall indicate the frame from
  // which the child frame was activated." The outermost frame of a call chain
  // was activated from no frame, so it hangs off the thread instead, which is
  // the diagram's frame--thread edge and reports no parent frame.
  VpiHandle holder = outer != nullptr ? outer : thread;
  if (holder == nullptr) return nullptr;

  // A call chain of the same shape entered again reuses the frame already made
  // at this point in it. Detail 4 has at most one frame active at a time in a
  // thread, and what tells one activation from the next is which frame is
  // active rather than which object stands for it -- a design calling a
  // function a thousand times has one frame a thousand times over, not a
  // thousand objects.
  VpiObject* frame = FirstChildOfType(holder, vpiFrame);
  if (frame == nullptr) {
    frame = AllocObject();
    frame->type = vpiFrame;
    frame->parent = holder;
    holder->children.push_back(frame);
  }
  frame->active = true;
  active_frame_ = frame;
  return outer;
}

void VpiContext::RestoreActiveFrame(VpiHandle previous) {
  if (sim_ctx_ == nullptr) return;
  // §37.43 (vpiActive): the frame being left is no longer the active one, and
  // the frame it was activated from becomes active again.
  if (active_frame_ != nullptr) active_frame_->active = false;
  active_frame_ = previous;
  if (active_frame_ != nullptr) active_frame_->active = true;
}

VpiActiveFrameScope::VpiActiveFrameScope()
    : outer_(GetGlobalVpiContext().ActivateFrame()) {}

VpiActiveFrameScope::~VpiActiveFrameScope() {
  GetGlobalVpiContext().RestoreActiveFrame(outer_);
}

namespace {

// §37.14: the vpiDirection a declared port reports. A port declared with no
// direction, and §13's ref direction, which the diagram's port has no value
// for, report none.
int VpiPortDirectionOf(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return kVpiInput;
    case Direction::kOutput:
      return kVpiOutput;
    case Direction::kInout:
      return kVpiInout;
    default:
      return 0;
  }
}

// One port of a module instance, as the object §37.14's instance-to-port
// relation reaches. `index` is the position the module declared it in, which
// detail 9 has vpiPortIndex report and which starts at zero, and `size` is the
// width detail 6 has vpiScalar and vpiVector read -- "whether the port is 1 bit
// or more than 1 bit ... not anything about what is connected to the port".
void FillPortObject(VpiObject* obj, const RtlirPort& port, int index,
                    VpiHandle module, std::deque<std::string>& names) {
  obj->type = kVpiPort;
  names.emplace_back(port.name);
  obj->name = names.back();
  obj->index = index;
  obj->size = static_cast<int>(port.width);
  obj->direction = VpiPortDirectionOf(port.direction);
  obj->parent = module;
  module->children.push_back(obj);
}

// The instances `mod` holds, pushed onto the walk under their own paths. An
// instance's path is its parent's with its name on the end, which is the string
// the simulator keys every object of that instance under.
void PushChildInstances(
    const RtlirModule* mod, const std::string& prefix,
    std::vector<std::pair<const RtlirModule*, std::string>>& work) {
  work.reserve(work.size() + mod->children.size());
  for (const auto& child : mod->children) {
    std::string child_prefix = prefix;
    if (!child_prefix.empty()) child_prefix += '.';
    child_prefix += std::string(child.inst_name);
    work.emplace_back(child.resolved, child_prefix);
  }
}

}  // namespace

void VpiContext::AttachDesignPorts(const RtlirDesign* design) {
  // §37.14: the ports a module instance declares, as the objects the diagram's
  // one-to-many instance-to-port relation reaches. VpiContext::CreatePort could
  // make one and nothing under src/ called it, so a design's ports were not
  // objects at all and the whole of §37.14 answered only for ports a test built
  // itself.
  if (design == nullptr) return;

  // The instance paths, walked outward from each top. A top module carries the
  // empty prefix and has no module object over it to hang ports from, the same
  // boundary the module paths meet.
  std::vector<std::pair<const RtlirModule*, std::string>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) work.emplace_back(top, std::string());

  while (!work.empty()) {
    auto [mod, prefix] = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    PushChildInstances(mod, prefix, work);
    if (prefix.empty()) continue;

    VpiHandle module = DesignObjectForFlatName(prefix);
    if (module == nullptr) continue;

    module->children.reserve(module->children.size() + mod->ports.size());
    int index = 0;
    for (const auto& port : mod->ports) {
      FillPortObject(AllocObject(), port, index++, module, name_pool_);
    }
  }
}

namespace {

// §37.37: one end of an intermodule path as the connection that makes the path
// names it -- the instance whose port it is, the port's own name, the signal of
// the enclosing scope the instantiation connected it to, and the direction that
// says which end of a path the port can be.
struct InterModPortRef {
  std::string inst_path;
  std::string_view port_name;
  std::string_view signal;
  Direction direction;
};

// §37.37: one intermodule path, as the two ports it runs between.
struct InterModConnection {
  std::string from_inst;
  std::string_view from_port;
  std::string to_inst;
  std::string_view to_port;
};

// The signal of the enclosing scope a port connection names. §23.3.2 lets the
// actual be an expression, and an expression names no single signal two ports
// can both be on, so only a connection written as a plain name puts its port
// where a path can reach it.
std::string_view ConnectedSignalName(const Expr* conn) {
  if (conn == nullptr || conn->kind != ExprKind::kIdentifier) return {};
  return conn->text;
}

// §37.37: an intermodule path runs from the port driving a signal to a port
// receiving it, which makes an inout port either end and a port that is neither
// no end at all. The two ends are distinct ports of one signal.
bool InterModPathRuns(const InterModPortRef& from, const InterModPortRef& to) {
  if (&from == &to) return false;
  if (from.signal != to.signal) return false;
  const bool kDrives = from.direction == Direction::kOutput ||
                       from.direction == Direction::kInout;
  const bool kReceives =
      to.direction == Direction::kInput || to.direction == Direction::kInout;
  return kDrives && kReceives;
}

// Every port the instances of `mod` connect to a signal of `mod`'s own scope.
// A path within this scope runs between two of them.
void CollectScopePortRefs(const RtlirModule* mod, const std::string& prefix,
                          std::vector<InterModPortRef>& refs) {
  for (const auto& child : mod->children) {
    std::string inst_path = prefix;
    if (!inst_path.empty()) inst_path += '.';
    inst_path += std::string(child.inst_name);
    refs.reserve(refs.size() + child.port_bindings.size());
    for (const auto& binding : child.port_bindings) {
      std::string_view signal = ConnectedSignalName(binding.connection);
      if (signal.empty()) continue;
      refs.push_back({inst_path, binding.port_name, signal, binding.direction});
    }
  }
}

// The paths running out of one port: one to each port of the same signal that
// receives what this one drives.
void PairOnePortRef(const InterModPortRef& from,
                    const std::vector<InterModPortRef>& refs,
                    std::vector<InterModConnection>& out) {
  out.reserve(out.size() + refs.size());
  for (const auto& to : refs) {
    if (!InterModPathRuns(from, to)) continue;
    out.push_back({from.inst_path, from.port_name, to.inst_path, to.port_name});
  }
}

// The paths one scope's connections make: every ordered pair of that scope's
// connected ports a signal runs between.
void PairScopePortRefs(const std::vector<InterModPortRef>& refs,
                       std::vector<InterModConnection>& out) {
  for (const auto& from : refs) PairOnePortRef(from, refs, out);
}

// Every intermodule path the design makes, gathered by walking the instance
// paths outward from each top the way the ports themselves are.
void CollectInterModConnections(const RtlirDesign* design,
                                std::vector<InterModConnection>& out) {
  std::vector<std::pair<const RtlirModule*, std::string>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) work.emplace_back(top, std::string());

  while (!work.empty()) {
    auto [mod, prefix] = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    PushChildInstances(mod, prefix, work);
    // A path is a connection between two of one scope's instances, so the
    // scope holding the instantiations is where both its ends are named.
    std::vector<InterModPortRef> refs;
    CollectScopePortRefs(mod, prefix, refs);
    PairScopePortRefs(refs, out);
  }
}

// The port object one end of a path names, which AttachDesignPorts made. A
// connection naming a port its module does not declare has none to name.
VpiObject* DesignPortObject(VpiHandle module, std::string_view port_name) {
  if (module == nullptr) return nullptr;
  for (auto* child : module->children) {
    if (child->type == kVpiPort && child->name == port_name) return child;
  }
  return nullptr;
}

}  // namespace

void VpiContext::AttachDesignInterModPaths(const RtlirDesign* design) {
  // §37.37: an intermodule path runs between the ports of two module instances,
  // and detail 1 says how a PLI application gets to one -- "vpi_handle_multi(
  // vpiInterModPath, port1, port2) can be used". Nothing under src/ made one,
  // so a run held no intermodule path at all and the whole of this model
  // answered for paths a test had built and for none a design connected.
  if (design == nullptr) return;

  std::vector<InterModConnection> conns;
  CollectInterModConnections(design, conns);
  for (const InterModConnection& conn : conns) {
    VpiObject* from = DesignPortObject(DesignObjectForFlatName(conn.from_inst),
                                       conn.from_port);
    VpiObject* to =
        DesignPortObject(DesignObjectForFlatName(conn.to_inst), conn.to_port);
    if (from == nullptr || to == nullptr) continue;

    auto* path = AllocObject();
    path->type = vpiInterModPath;
    // §37.37 (the diagram's one-to-many relation to ports): the ports the path
    // runs between, and the link back from each of them, which is where
    // vpi_handle_multi() finds the path the two ports are both on.
    path->children.push_back(from);
    path->children.push_back(to);
    from->children.push_back(path);
    to->children.push_back(path);
  }
}

void VpiContext::AttachModuleDefNames(SimContext& sim_ctx) {
  // §38.11's example is what a definition name is for: vpi_handle_by_name
  // reaches an instance and vpi_get_str(vpiDefName, mod) says what it is an
  // instance of -- "Module top.mod1 is an instance of %s". The instance's own
  // name is vpiName and is the answer to a different question, so a module
  // reporting it here said that top.mod1 is an instance of mod1.
  //
  // The run has the answer already: the lowerer records each instance's module
  // type against the instance path, which is the same string the module object
  // carries as its vpiFullName.
  for (auto* obj : all_objects_) {
    if (obj->type != kVpiModule || obj->full_name.empty()) continue;
    std::string_view type = sim_ctx.FindInstanceType(obj->full_name);
    if (!type.empty()) obj->def_name = std::string(type);
  }
}

void VpiContext::AttachModulePathDelays(SimContext& sim_ctx) {
  // §38.10: "the VPI routine vpi_get_delays() shall retrieve the delays or
  // pulse limits of an object". A module path is one of the four kinds of
  // object the clause gives legal no_of_delays values for, and it is the one
  // whose twelve transition delays the clause takes without interpreting them
  // -- the 12-value row of Table 38-2 is the path's own array. No object a run
  // built carried a delay at all, so the routine had only what a caller put in
  // an object of its own making to retrieve.
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;

  for (const PathDelay& path : specify->GetPathDelays()) {
    // §30.3 puts a specify block inside a module declaration, so the paths it
    // declares belong to the instance that declared them. A path of a module
    // elaborated as a top carries the empty prefix and has no module object
    // over it to hang from.
    if (path.inst_prefix.empty()) continue;
    std::string_view scope = path.inst_prefix;
    scope.remove_suffix(1);  // the prefix ends in the separator
    VpiHandle module = DesignObjectForFlatName(scope);
    if (module == nullptr) continue;

    auto* obj = AllocObject();
    obj->type = vpiModPath;
    obj->parent = module;
    module->children.push_back(obj);
    // §38.10: "the application-allocated s_vpi_delay array shall contain delays
    // in the same order in which they occur in the SystemVerilog description",
    // which for a module path is the order of its transition slots, and the
    // pulse limits §30.7 gives each of them travel with each delay.
    obj->delays.reserve(path.delay_count);
    for (uint8_t i = 0; i < path.delay_count; ++i) {
      VpiDelayInfo info;
      info.delay = static_cast<double>(path.delays[i]);
      info.min_delay = info.delay;
      info.typ_delay = info.delay;
      info.max_delay = info.delay;
      info.reject = static_cast<double>(path.reject_limit[i]);
      info.min_reject = info.reject;
      info.typ_reject = info.reject;
      info.max_reject = info.reject;
      info.error = static_cast<double>(path.error_limit[i]);
      info.min_error = info.error;
      info.typ_error = info.error;
      info.max_error = info.error;
      obj->delays.push_back(info);
    }
  }
}

void VpiContext::Attach(SimContext& sim_ctx) {
  // §37.44: the run the thread objects are made against. They cannot all be
  // made here -- a fork branch begins while the design executes, long after
  // this -- so what is kept is the run itself.
  sim_ctx_ = &sim_ctx;

  // §36.10: "VPI routines provide access to objects in an instantiated
  // SystemVerilog design. An instantiated design is one where each instance of
  // an object is uniquely accessible. For instance, if a module m contains wire
  // w and is instantiated twice as m1 and m2, then m1.w and m2.w are two
  // distinct objects, each with its own set of related objects and properties."
  //
  // The simulator has that already: it keys each instance's object on a flat
  // string carrying the instance prefix, so m1.w and m2.w are two entries over
  // two Nets. What was missing was the shape §38.21 walks -- the name was
  // entered whole and resolved a component at a time, so nothing but a
  // top-level name ever matched -- and the nets, which were not entered at all
  // though a wire is the clause's own example of an object VPI reaches.
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || var == nullptr) continue;
    obj->type = kVpiReg;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
  }
  AttachModuleDefNames(sim_ctx);
  AttachModulePathDelays(sim_ctx);
  for (auto& [name, net] : sim_ctx.GetNets()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || net == nullptr) continue;
    obj->type = kVpiNet;
    obj->net = net;
    // The same pairing CreateNetObj makes: a net answers a value query out of
    // the storage its resolution writes, so the object carries that storage
    // beside the net itself.
    if (net->resolved != nullptr) {
      obj->var = net->resolved;
      obj->size = static_cast<int>(net->resolved->value.width);
    }
  }
}

void AttachDesignToPliApplications(const RtlirDesign* design, SimContext& ctx) {
  VpiContext& vpi = GetGlobalVpiContext();
  // §36.9's two registrations are what a PLI application has become part of
  // this tool by, so between them they say whether the run holds one at all.
  // A run holding neither has nobody to call the library, and the design it
  // would answer with is left unbuilt rather than built for no reader.
  if (vpi.RegisteredSystfs().empty() && vpi.RegisteredCallbacks().empty()) {
    return;
  }
  vpi.Attach(ctx);
  vpi.AttachDesignPorts(design);
  // §37.37: the paths run between the port objects the line above made, so they
  // are gathered once those exist.
  vpi.AttachDesignInterModPaths(design);
}

}  // namespace delta
