#include <algorithm>
#include <iterator>
#include <string>
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
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_stmt_objects.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiObject* VpiStmtObjectFor(const VpiStmtObjects& stmts, const Stmt* stmt,
                            std::string prefix) {
  if (stmt == nullptr) return nullptr;
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  auto found = stmts.find({stmt, prefix});
  if (found == stmts.end()) found = stmts.lower_bound({stmt, std::string()});
  if (found == stmts.end() || found->first.first != stmt) return nullptr;
  return found->second;
}

VpiObject* VpiCallSiteObjectFor(const VpiCallSiteObjects& sites,
                                const Expr* call_site, std::string prefix) {
  if (!prefix.empty()) prefix.pop_back();
  auto exact = sites.find({call_site, prefix});
  if (exact != sites.end()) return exact->second;
  auto first = sites.lower_bound({call_site, std::string()});
  if (first == sites.end() || first->first.first != call_site) return nullptr;
  auto next = std::next(first);
  const bool kOnly = next == sites.end() || next->first.first != call_site;
  return kOnly ? first->second : nullptr;
}

namespace {

thread_local bool g_making_forking_thread = false;

}  // namespace

VpiHandle VpiContext::ThreadObjectFor(Process* proc) {
  if (proc == nullptr) return nullptr;
  auto it = run_objects_.find(proc);
  if (it != run_objects_.end()) {
    it->second->active = proc->active;
    return it->second;
  }
  auto* obj = AllocObject();
  obj->type = vpiThread;
  obj->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);
  obj->active = proc->active;
  obj->body = VpiStmtObjectFor(stmt_objects_, proc->origin, proc->inst_prefix);
  run_objects_[proc] = obj;
  const bool kBeginning = !g_making_forking_thread;
  if (sim_ctx_ != nullptr) {
    const std::vector<Process*>& threads = sim_ctx_->GetScheduler().Threads();
    auto forking = std::ranges::find_if(threads, [proc](const Process* p) {
      return std::ranges::find(p->children, proc) != p->children.end();
    });
    if (forking != threads.end()) {
      g_making_forking_thread = true;
      VpiHandle parent = ThreadObjectFor(*forking);
      g_making_forking_thread = !kBeginning;
      obj->parent = parent;
      parent->children.push_back(obj);
    }
  }
  if (kBeginning) DispatchCallbacks(cbStartOfThread, obj);
  return obj;
}

void VpiContext::NoteThreadEnded(Process* proc) {
  if (sim_ctx_ == nullptr) return;
  if (!run_objects_.contains(proc) &&
      !HasCallbackFor(callbacks_, cbEndOfThread)) {
    return;
  }
  ReleaseFrameOrThreadObject(ThreadObjectFor(proc));
}

void VpiContext::NoteThreadEntered(Process* proc) {
  if (sim_ctx_ == nullptr || !HasCallbackFor(callbacks_, cbEnterThread)) {
    return;
  }
  DispatchCallbacks(cbEnterThread, ThreadObjectFor(proc));
}

void VpiContext::RefreshRunObjects() {
  RefreshThreadObjects();
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
    ThreadObjectFor(proc);
    for (Process* child : proc->children) ThreadObjectFor(child);
  }
}

namespace {

VpiObject* FirstChildOfType(VpiObject* obj, int type) {
  if (obj == nullptr) return nullptr;
  for (auto* child : obj->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

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

VpiHandle VpiContext::ActivateFrame(const void*& thread, const Expr* call) {
  if (sim_ctx_ == nullptr) return nullptr;

  thread = FrameThreadOf(sim_ctx_);
  VpiHandle outer = ActiveFrame();
  VpiHandle proc_thread = ThreadObjectFor(sim_ctx_->CurrentProcess());
  VpiHandle holder = outer != nullptr ? outer : proc_thread;
  if (holder == nullptr) return nullptr;

  VpiObject* frame = FirstChildOfType(holder, vpiFrame);
  if (frame == nullptr) {
    frame = AllocObject();
    frame->type = vpiFrame;
    frame->alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);
    frame->parent = holder;
    holder->children.push_back(frame);
  }
  frame->released = false;
  frame->active = true;
  frame->frame_facts = {
      .origin = VpiCallSiteObjectFor(call_site_objects_, call,
                                     sim_ctx_->ActiveInstancePrefix()),
      .stmt = nullptr};
  active_frames_[thread] = frame;
  DispatchCallbacks(cbStartOfFrame, frame);
  return outer;
}

void VpiContext::RestoreActiveFrame(VpiHandle previous, const void* thread) {
  if (sim_ctx_ == nullptr) return;
  VpiHandle& active = active_frames_[thread];
  if (active != nullptr) {
    ReleaseFrameOrThreadObject(active);
    active->active = false;
  }
  active = previous;
  if (active != nullptr) active->active = true;
}

VpiActiveFrameScope::VpiActiveFrameScope(const Expr* call)
    : outer_(GetGlobalVpiContext().ActivateFrame(thread_, call)) {}

VpiActiveFrameScope::~VpiActiveFrameScope() {
  GetGlobalVpiContext().RestoreActiveFrame(outer_, thread_);
}

}  // namespace delta
