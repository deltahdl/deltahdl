#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
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
