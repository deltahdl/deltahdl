#include "simulation/scheduler.h"

#include <cassert>

#include "common/arena.h"

namespace delta {

// --- EventPool ---

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
  event->next = free_list_;
  free_list_ = event;
  ++free_count_;
}

// --- EventQueue ---

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

// --- TimeSlot ---

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

// --- Scheduler: public interface ---

void Scheduler::ScheduleEvent(SimTime time, Region region, Event* event) {
  assert(!(time < current_time_));
  auto idx = static_cast<size_t>(region);
  event_calendar_[time].regions[idx].Push(event);
}

void Scheduler::Run() {
  while (!event_calendar_.empty() && !stop_requested_) {
    auto it = event_calendar_.begin();
    current_time_ = it->first;
    ExecuteTimeSlot(it->second);
    event_calendar_.erase(it);
  }
}

// --- Scheduler: time slot execution (IEEE 1800-2023 section 4.5) ---

void Scheduler::ExecuteTimeSlot(TimeSlot& slot) {
  // Preponed region: read-only sampling
  ExecuteRegion(slot.regions[static_cast<size_t>(Region::kPreponed)]);

  // Iterate Active region set until stable
  while (IterateActiveSet(slot)) {
    // Keep iterating while events exist in active regions
  }

  // Iterate Reactive region set until stable
  while (IterateReactiveSet(slot)) {
    // Keep iterating while events exist in reactive regions
  }

  // Postponed region
  ExecuteRegion(slot.regions[static_cast<size_t>(Region::kPostponed)]);
}

// --- Scheduler: Active region set iteration ---
// Regions: PreActive, Active, Inactive, PreNBA, NBA, PostNBA

bool Scheduler::IterateActiveSet(TimeSlot& slot) {
  bool did_work = false;

  ExecuteActiveRegions(slot);
  if (slot.AnyNonemptyIn(Region::kPreActive, Region::kPostNBA)) {
    did_work = true;
  }

  // Drain all active-side regions in priority order
  while (slot.AnyNonemptyIn(Region::kPreActive, Region::kPostNBA)) {
    ExecuteActiveRegions(slot);
  }

  return did_work;
}

void Scheduler::ExecuteActiveRegions(TimeSlot& slot) {
  auto exec = [&](Region r) {
    ExecuteRegion(slot.regions[static_cast<size_t>(r)]);
  };

  exec(Region::kPreActive);
  exec(Region::kActive);
  exec(Region::kInactive);
  exec(Region::kPreNBA);
  exec(Region::kNBA);
  exec(Region::kPostNBA);
}

// --- Scheduler: Reactive region set iteration ---
// Regions: PreObserved, Observed, PostObserved, Reactive,
//          ReInactive, PreReNBA, ReNBA, PostReNBA, PrePostponed

bool Scheduler::IterateReactiveSet(TimeSlot& slot) {
  bool did_work = false;

  ExecuteReactiveRegions(slot);
  if (slot.AnyNonemptyIn(Region::kPreObserved, Region::kPrePostponed)) {
    did_work = true;
  }

  while (slot.AnyNonemptyIn(Region::kPreObserved, Region::kPrePostponed)) {
    ExecuteReactiveRegions(slot);
    RestartActiveSet(slot);
  }

  return did_work;
}

void Scheduler::RestartActiveSet(TimeSlot& slot) {
  if (!slot.AnyNonemptyIn(Region::kPreActive, Region::kPostNBA)) return;
  while (IterateActiveSet(slot)) {
  }
}

void Scheduler::ExecuteReactiveRegions(TimeSlot& slot) {
  auto exec = [&](Region r) {
    ExecuteRegion(slot.regions[static_cast<size_t>(r)]);
  };

  exec(Region::kPreObserved);
  exec(Region::kObserved);
  exec(Region::kPostObserved);
  exec(Region::kReactive);
  exec(Region::kReInactive);
  exec(Region::kPreReNBA);
  exec(Region::kReNBA);
  exec(Region::kPostReNBA);
  exec(Region::kPrePostponed);
}

// --- Scheduler: single region drain ---

void Scheduler::ExecuteRegion(EventQueue& queue) {
  while (!queue.empty()) {
    Event* event = queue.Pop();
    if (event->callback) {
      event->callback();
    }
    pool_.Release(event);
  }
}

}  // namespace delta
