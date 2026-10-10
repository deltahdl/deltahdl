#include "simulator/scheduler.h"

#include <cstdio>
#include <cstdlib>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

Event* EventPool::Acquire() {
  if (free_list_) {
    Event* event = free_list_;
    free_list_ = event->next;
    --free_count_;
    event->next = nullptr;
    return event;
  }
  return arena_.Create<Event>();
}

void EventPool::Release(Event* event) {
  event->kind = EventKind::kEvaluation;
  event->target = nullptr;
  event->callback = nullptr;
  event->superseded = nullptr;
  event->next = free_list_;
  free_list_ = event;
  ++free_count_;
}

void EventQueue::Push(Event* event) {
  event->next = nullptr;
  if (tail) {
    tail->next = event;
  } else {
    head = event;
  }
  tail = event;
}

Event* EventQueue::Pop() {
  if (!head) {
    return nullptr;
  }
  Event* event = head;
  head = head->next;
  if (!head) {
    tail = nullptr;
  }
  event->next = nullptr;
  return event;
}

void EventQueue::Clear() {
  head = nullptr;
  tail = nullptr;
}

bool TimeSlot::AnyNonemptyIn(Region first, Region last) const {
  auto lo = static_cast<size_t>(first);
  auto hi = static_cast<size_t>(last);
  for (size_t i = lo; i <= hi; ++i) {
    if (!regions[i].empty()) {
      return true;
    }
  }
  return false;
}

Region TimeSlot::FirstNonemptyIn(Region first, Region last) const {
  auto lo = static_cast<size_t>(first);
  auto hi = static_cast<size_t>(last);
  for (size_t i = lo; i <= hi; ++i) {
    if (!regions[i].empty()) {
      return static_cast<Region>(i);
    }
  }
  return Region::kCOUNT;
}

bool TimeSlot::AnyIterativeNonempty() const {
  for (size_t i = 0; i < kRegionCount; ++i) {
    if (IsIterativeRegion(static_cast<Region>(i)) && !regions[i].empty()) {
      return true;
    }
  }
  return false;
}

void Scheduler::ScheduleEvent(SimTime time, Region region, Event* event) {
  if (time < current_time_) {
    std::fprintf(
        stderr,
        "scheduler: refusing to schedule event at past time %llu "
        "(current=%llu); §4.4 ¶2 forbids backwards-in-time scheduling\n",
        static_cast<unsigned long long>(time.ticks),
        static_cast<unsigned long long>(current_time_.ticks));
    std::abort();
  }

  if (event->kind == EventKind::kPli && region == Region::kObserved) {
    ++illegal_observed_pli_count_;
    pool_.Release(event);
    return;
  }

  if (current_region_ == Region::kPreponed && time == current_time_ &&
      region != Region::kPreponed) {
    ++illegal_preponed_schedule_count_;
  }

  if (current_region_ == Region::kPostponed && time == current_time_ &&
      region != Region::kPostponed) {
    ++illegal_postponed_schedule_count_;
  }

  // §4.4.3.5: the Pre-Observed region only lets PLI routines read the
  // stabilized active region set; scheduling any event into the current time
  // slot from within it is illegal.
  if (current_region_ == Region::kPreObserved && time == current_time_) {
    ++illegal_pre_observed_schedule_count_;
  }

  if (event->kind == EventKind::kUpdate) {
    ++update_events_scheduled_count_;
  } else {
    ++evaluation_events_scheduled_count_;
  }
  auto idx = static_cast<size_t>(region);
  event_calendar_[time].regions[idx].Push(event);
}

static bool SlotHasLiveEvent(const TimeSlot& slot) {
  for (const auto& queue : slot.regions) {
    for (const Event* e = queue.head; e; e = e->next) {
      if (!e->superseded || !*e->superseded) return true;
    }
  }
  return false;
}

bool Scheduler::Halted() const {
  return ctx_ != nullptr && ctx_->FinishRequested();
}

bool Scheduler::ProgramsEnded() const {
  return ctx_ != nullptr && ctx_->ProgramsEnded();
}

void Scheduler::ReleaseSlot(TimeSlot& slot) {
  for (auto& queue : slot.regions) {
    while (!queue.empty()) pool_.Release(queue.Pop());
  }
}

void Scheduler::Run() {
  // §38.36.3: cbStartOfSimulation marks the start of simulation, the beginning
  // of the time zero cycle. It is one of the action reasons, which the clause
  // separates from the feature reasons by requiring every VPI-compliant tool to
  // raise them, and this is where simulation starts: the design
  // is built and no event has run.
  GetGlobalVpiContext().DispatchCallbacks(kCbStartOfSimulation);

  // §20.2: an explicit $finish/$stop/$fatal requests a hard halt through the
  // SimContext, and the run ends where it was called. No later time slot runs
  // -- a process suspended on a delay must not resume in a time step past the
  // finish (e.g. `forever #10` with `#45 $finish` performs its t=40 iteration
  // but not the t=50 one) -- and ExecuteTimeSlot stops the slot the halt came
  // in, whose remaining events are released here unrun.
  //
  // §24.3: the implicit $finish due once every program initial has ended
  // (ProgramsEnded) ends the run when the time slot it came in is done. The
  // rest of that slot runs, the design's side of a port the program wrote in
  // it among them, and no later slot does: a design process waiting on a
  // delay past the program's end never resumes.
  while (!event_calendar_.empty() && !stop_requested_ && !Halted() &&
         !ProgramsEnded()) {
    auto it = event_calendar_.begin();
    if (!SlotHasLiveEvent(it->second)) {
      // Every event here is a superseded inertial-delay timeout that an earlier
      // operand change cancelled (IEEE 1800 §28). They do no work, so drop them
      // without advancing simulation time past the last real activity.
      ReleaseSlot(it->second);
      event_calendar_.erase(it);
      continue;
    }
    current_time_ = it->first;
    ExecuteTimeSlot(it->second);
    ReleaseSlot(it->second);
    event_calendar_.erase(it);
  }
  // The scheduler is now idle: no process is executing. An event callback that
  // resumed a process left it installed as the context's current process (that
  // is how a bare-name lookup during the process picks up its instance prefix).
  // Clear it so a post-run hierarchical lookup - e.g. a testbench or PLI query
  // after Run() returns - resolves in the top scope instead of inheriting the
  // last-run instance's prefix and finding a same-named variable it shadows.
  if (ctx_) ctx_->SetCurrentProcess(nullptr);
  if (ProgramsEnded()) ctx_->RequestStop();

  // §38.36.3: cbEndOfSimulation marks the end of simulation, whether the event
  // queue ran empty or a $finish executed. Both are how the loop above ends.
  GetGlobalVpiContext().DispatchCallbacks(kCbEndOfSimulation);
}

// §20.2 with §9.2.3: once a halt is requested the slot runs no further event,
// whatever region it waits in, so a nonblocking update, a deferred assertion's
// pending report (§16.4.1) or a $strobe (§21.2.2) queued behind the $finish in
// its own time step is never reached. The post-timestep callbacks still run:
// they record what the slot did before the halt, such as the value changes a
// VCD dump writes for it, and execute no scheduled event.
void Scheduler::ExecuteTimeSlot(TimeSlot& slot) {
  ExecuteRegion(slot, Region::kPreponed);

  // §38.36.2: a cbNextSimTime callback is called before the events of the
  // next time slot, the first after the one it was registered in, and Table
  // 4-1 places it in the Pre-Active region, which §4.5 enters after the
  // Preponed region has sampled the slot.
  current_region_ = Region::kPreActive;
  GetGlobalVpiContext().DispatchCallbacks(kCbNextSimTime);
  ExecuteRegion(slot, Region::kPreActive);

  while (!Halted() && slot.AnyIterativeNonempty()) {
    while (IterateActiveSet(slot)) {
    }
    while (IterateReactiveSet(slot)) {
    }

    if (!Halted() && !slot.AnyNonemptyIn(Region::kActive, Region::kPostReNBA)) {
      ExecuteRegion(slot, Region::kPrePostponed);
    }
  }

  if (!Halted()) ExecuteRegion(slot, Region::kPostponed);

  current_region_ = Region::kCOUNT;
  for (const auto& cb : post_timestep_cbs_) cb();
}

bool Scheduler::IterateActiveSet(TimeSlot& slot) {
  if (Halted() || !slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    return false;
  }
  // §4.5 reference algorithm: drain the active region set together with the
  // Observed regions, always taking the *earliest* nonempty region next. An
  // event scheduled into an earlier region while a later one runs (e.g. an NBA
  // created during the Observed region) is therefore processed before the
  // reactive set, and the Pre-Observed/Observed regions sample only once every
  // earlier active-set region — including Inactive→Active re-entries — settles.
  while (!Halted() &&
         slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    ExecuteIterativeRegion(
        slot, slot.FirstNonemptyIn(Region::kActive, Region::kPostObserved),
        Region::kActive);
  }
  return true;
}

bool Scheduler::IterateReactiveSet(TimeSlot& slot) {
  if (Halted() || !slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    return false;
  }
  // §4.5 reference algorithm: same earliest-nonempty-first drain across the
  // reactive region set (Reactive..Post-Re-NBA).
  while (!Halted() &&
         slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    ExecuteIterativeRegion(
        slot, slot.FirstNonemptyIn(Region::kReactive, Region::kPostReNBA),
        Region::kReactive);
  }
  return true;
}

// §4.5 moves the events of the first nonempty region after `home` -- the
// Active region, or the Reactive region for the reactive set -- into `home`
// and executes `home`, so an event scheduled into that region while they run
// stays there until `home` is empty again: a process resumed from `#0` in the
// Inactive region that writes a variable and executes `#0` again resumes after
// the Active events its write created (§4.4.2.3, §4.4.2.7). The region runs in
// place, keeping its own identity for the region checks, but only the events
// it held on entry.
void Scheduler::ExecuteIterativeRegion(TimeSlot& slot, Region region,
                                       Region home) {
  if (region == home) {
    ExecuteRegion(slot, region);
    return;
  }
  current_region_ = region;
  EventQueue& queue = slot.regions[static_cast<size_t>(region)];
  const Event* const kLastOnEntry = queue.tail;
  const Event* ran = nullptr;
  do {
    Event* event = queue.Pop();
    ran = event;
    RunEvent(event);
  } while (ran != kLastOnEntry && !Halted());
}

void Scheduler::ExecuteRegion(TimeSlot& slot, Region region) {
  current_region_ = region;
  DrainQueue(slot.regions[static_cast<size_t>(region)]);
}

void Scheduler::DrainQueue(EventQueue& queue) {
  while (!queue.empty() && !Halted()) RunEvent(queue.Pop());
}

void Scheduler::RunEvent(Event* event) {
  if (event->callback) event->callback();
  pool_.Release(event);
}

}  // namespace delta
