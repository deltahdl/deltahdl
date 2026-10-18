#include <unordered_map>
#include <utility>
#include <vector>

#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// The threads and frames of a run (§37.43, §37.44): the objects the model
// makes for the run's processes and for the frames their call chains activate,
// and the ends of their lives, which release their handles (§37.2.2).

namespace delta {

VpiHandle VpiContext::ThreadObjectFor(Process* proc) {
  if (proc == nullptr) return nullptr;
  auto it = run_objects_.find(proc);
  if (it != run_objects_.end()) {
    // §37.44 (vpiActive): the property belongs to the process, so it is read
    // when asked for rather than frozen into the object when it was made.
    it->second->active = proc->active;
    return it->second;
  }
  auto* obj = AllocObject();
  obj->type = vpiThread;
  // §37.3.7: a thread has the lifetime of the thread it is.
  obj->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);
  obj->active = proc->active;
  run_objects_[proc] = obj;
  // §37.3.8: a thread is one of the transient objects callbacks can follow
  // through its life, and cbStartOfThread is the one that
  // reports its beginning. This is where the thread becomes an object of the
  // model, and no site delivered the callback at all.
  DispatchCallbacks(cbStartOfThread, obj);
  return obj;
}

void VpiContext::NoteThreadEnded(Process* proc) {
  // §37.2.2 item 2 and §37.3.8: a thread that ends releases the handles to it
  // and to the objects belonging to it, and cbEndOfThread reports the end. A
  // thread no application asked for has no object, and is made one only where
  // a cbEndOfThread callback is there to be told of its end.
  if (sim_ctx_ == nullptr) return;
  if (!run_objects_.contains(proc) &&
      !HasCallbackFor(callbacks_, cbEndOfThread)) {
    return;
  }
  ReleaseFrameOrThreadObject(ThreadObjectFor(proc));
}

void VpiContext::RefreshRunObjects() {
  RefreshThreadObjects();
  // §37.81: the time queue a run's iteration walks is its scheduler's slots
  // still holding events, the current one marked; a context no run is
  // attached to keeps the slots it was given.
  if (sim_ctx_ == nullptr) return;
  const Scheduler& scheduler = sim_ctx_->GetScheduler();
  std::vector<VpiTimeQueueSlot> slots;
  for (const PendingTimeSlot& pending : scheduler.PendingTimeSlots()) {
    slots.push_back({pending.time.ticks,
                     pending.time == scheduler.CurrentTime(),
                     pending.before_read_only_synch});
  }
  time_queue_slots_ = std::move(slots);
}

void VpiContext::RefreshThreadObjects() {
  if (sim_ctx_ == nullptr) return;
  for (Process* proc : sim_ctx_->GetScheduler().Threads()) {
    VpiHandle obj = ThreadObjectFor(proc);
    // §37.44 (thread one-to-many thread): the threads this one spawned, which
    // detail 1 counts as threads, being branches of a fork. They hang off the
    // parent as its thread children, which is where VpiThreadThreads reads them
    // and where VpiThreadParent reads the link back.
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

// The thread a frame is active in: the process the run is executing, null
// outside one, as when a case drives the context by hand.
const void* FrameThreadOf(SimContext* sim_ctx) {
  return sim_ctx == nullptr ? nullptr : sim_ctx->CurrentProcess();
}

}  // namespace

void VpiContext::SetActiveFrame(VpiHandle frame) {
  active_frames_[FrameThreadOf(sim_ctx_)] = frame;
}

VpiHandle VpiContext::ActiveFrame() const {
  auto found = active_frames_.find(FrameThreadOf(sim_ctx_));
  return found == active_frames_.end() ? nullptr : found->second;
}

VpiHandle VpiContext::ActivateFrame(const void*& thread) {
  // §36.6: a run holding no PLI application has no design attached and nothing
  // to reach a frame through, so it pays nothing for this.
  if (sim_ctx_ == nullptr) return nullptr;

  // §37.43 detail 4: at most one frame is active at a time in each thread, so
  // the frame a call chain activates is kept with the thread it runs in. A
  // task suspended across time leaves its frame active in its own thread
  // while other threads activate and leave frames of their own.
  thread = FrameThreadOf(sim_ctx_);
  VpiHandle outer = ActiveFrame();
  VpiHandle proc_thread = ThreadObjectFor(sim_ctx_->CurrentProcess());
  // §37.43 detail 5: vpiParent of a frame is the frame it was activated from.
  // The outermost frame of a call chain
  // was activated from no frame, so it hangs off the thread instead, which is
  // the diagram's frame--thread edge and reports no parent frame.
  VpiHandle holder = outer != nullptr ? outer : proc_thread;
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
    frame->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);
    frame->parent = holder;
    holder->children.push_back(frame);
  }
  // §37.2.2: the frame the last activation ended released its handles; this
  // activation is a frame's life of its own, so its object is live again.
  frame->released = false;
  frame->active = true;
  active_frames_[thread] = frame;
  // §37.3.8: a frame is a transient object too, and cbStartOfFrame reports the
  // beginning of one. Detail 4 of §37.43 has at most one frame active at a time
  // in a thread, so the frame's life is the activation this ends rather than
  // the allocation above, which a call chain entered again reuses.
  DispatchCallbacks(cbStartOfFrame, frame);
  return outer;
}

void VpiContext::RestoreActiveFrame(VpiHandle previous, const void* thread) {
  if (sim_ctx_ == nullptr) return;
  // §37.43 (vpiActive): the frame being left is no longer the active one in
  // its thread, and the frame it was activated from becomes active again. The
  // thread is the one the frame was activated in, which a task torn down while
  // another thread runs still names.
  //
  // §37.3.8: leaving it ends that frame's life, which is what cbEndOfFrame is
  // there to report, and §37.2.2 item 2 has the end of a frame release the
  // handles to it and to the objects belonging to it.
  VpiHandle& active = active_frames_[thread];
  if (active != nullptr) {
    ReleaseFrameOrThreadObject(active);
    active->active = false;
  }
  active = previous;
  if (active != nullptr) active->active = true;
}

VpiActiveFrameScope::VpiActiveFrameScope()
    : outer_(GetGlobalVpiContext().ActivateFrame(thread_)) {}

VpiActiveFrameScope::~VpiActiveFrameScope() {
  GetGlobalVpiContext().RestoreActiveFrame(outer_, thread_);
}

}  // namespace delta
