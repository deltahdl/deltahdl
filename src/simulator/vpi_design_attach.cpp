#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
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
  for (Process* proc : sim_ctx_->GetThreads()) {
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

void AttachDesignToPliApplications(SimContext& ctx) {
  VpiContext& vpi = GetGlobalVpiContext();
  // §36.9's two registrations are what a PLI application has become part of
  // this tool by, so between them they say whether the run holds one at all.
  // A run holding neither has nobody to call the library, and the design it
  // would answer with is left unbuilt rather than built for no reader.
  if (vpi.RegisteredSystfs().empty() && vpi.RegisteredCallbacks().empty()) {
    return;
  }
  vpi.Attach(ctx);
}

}  // namespace delta
