#include "simulator/scheduler.h"

#include <cstdio>
#include <cstdlib>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_assertion_control.h"
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
  if (nba_capture_ != nullptr) {
    nba_capture_->emplace_back(event, region);
    return;
  }
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
  GetGlobalVpiContext().DispatchCallbacks(kCbStartOfSimulation);
  VpiStartAssertionSystem();

  while (!event_calendar_.empty() && !stop_requested_ && !Halted() &&
         !ProgramsEnded()) {
    auto it = event_calendar_.begin();
    if (!SlotHasLiveEvent(it->second)) {
      ReleaseSlot(it->second);
      event_calendar_.erase(it);
      continue;
    }
    current_time_ = it->first;
    ExecuteTimeSlot(it->second);
    ReleaseSlot(it->second);
    event_calendar_.erase(it);
    GetGlobalVpiContext().DeliverRaisedSignals();
    if (ctx_ != nullptr && ClassCollectionDue()) ctx_->CollectGarbage();
  }
  if (ctx_) ctx_->SetCurrentProcess(nullptr);
  if (ProgramsEnded()) ctx_->RequestStop();
}

void Scheduler::EndSimulation() {
  ctx_->RunFinalBlocks();
  GetGlobalVpiContext().DispatchCallbacks(kCbEndOfSimulation);
  VpiEndAssertionSystem();
}

void Scheduler::ExecuteTimeSlot(TimeSlot& slot) {
  ExecuteRegion(slot, Region::kPreponed);
  for (const auto& cb : time_slot_start_cbs_) cb();

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
  while (!Halted() &&
         slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    ExecuteIterativeRegion(
        slot, slot.FirstNonemptyIn(Region::kReactive, Region::kPostReNBA),
        Region::kReactive);
  }
  return true;
}

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

std::vector<PendingTimeSlot> Scheduler::PendingTimeSlots() const {
  std::vector<PendingTimeSlot> slots;
  for (const auto& [time, slot] : event_calendar_) {
    if (!slot.AnyNonemptyIn(Region::kPreponed, Region::kPostponed)) continue;
    slots.push_back(
        {time, slot.AnyNonemptyIn(Region::kPreponed, Region::kPrePostponed)});
  }
  return slots;
}

}  // namespace delta
