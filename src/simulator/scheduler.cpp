#include "simulator/scheduler.h"

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
  // §4.4.3.1: Within the Preponed region, it is illegal to schedule an
  // event in any other region within the current time slot.
  if (current_region_ == Region::kPreponed && time == current_time_ &&
      region != Region::kPreponed) {
    ++illegal_preponed_schedule_count_;
  }
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
  // Preponed region: read-only sampling (§4.4.2.1)
  ExecuteRegion(slot, Region::kPreponed);

  // Pre-Active region: PLI callback (§4.4.3.2)
  ExecuteRegion(slot, Region::kPreActive);

  // Iterative loop: [Active ... Pre-Postponed] (§4.5)
  while (slot.AnyNonemptyIn(Region::kActive, Region::kPrePostponed)) {
    while (IterateActiveSet(slot)) {
    }
    while (IterateReactiveSet(slot)) {
    }
    // Pre-Postponed only when [Active...Post-Re-NBA] are all empty
    if (!slot.AnyNonemptyIn(Region::kActive, Region::kPostReNBA)) {
      ExecuteRegion(slot, Region::kPrePostponed);
    }
  }

  // Postponed region: read-only (§4.4.3.10)
  ExecuteRegion(slot, Region::kPostponed);

  current_region_ = Region::kCOUNT;
  if (post_timestep_cb_) post_timestep_cb_();
}

// Inner active-set loop: iterates over Active..Post-Observed per §4.5.

bool Scheduler::IterateActiveSet(TimeSlot& slot) {
  if (!slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    return false;
  }
  while (slot.AnyNonemptyIn(Region::kActive, Region::kPostObserved)) {
    ExecuteActiveRegions(slot);
  }
  return true;
}

void Scheduler::ExecuteActiveRegions(TimeSlot& slot) {
  auto exec = [&](Region r) { ExecuteRegion(slot, r); };

  exec(Region::kActive);
  exec(Region::kInactive);
  exec(Region::kPreNBA);
  exec(Region::kNBA);
  exec(Region::kPostNBA);
  exec(Region::kPreObserved);
  exec(Region::kObserved);
  exec(Region::kPostObserved);
}

// Inner reactive-set loop: iterates over Reactive..Post-Re-NBA per §4.5.
// The outer loop in ExecuteTimeSlot re-enters the active-set loop once this
// returns, so events scheduled into the active set during reactive drain are
// processed only after the five reactive regions are fully drained.

bool Scheduler::IterateReactiveSet(TimeSlot& slot) {
  if (!slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    return false;
  }
  while (slot.AnyNonemptyIn(Region::kReactive, Region::kPostReNBA)) {
    ExecuteReactiveRegions(slot);
  }
  return true;
}

void Scheduler::ExecuteReactiveRegions(TimeSlot& slot) {
  auto exec = [&](Region r) { ExecuteRegion(slot, r); };

  exec(Region::kReactive);
  exec(Region::kReInactive);
  exec(Region::kPreReNBA);
  exec(Region::kReNBA);
  exec(Region::kPostReNBA);
}

// --- Scheduler: single region drain ---

void Scheduler::ExecuteRegion(TimeSlot& slot, Region region) {
  current_region_ = region;
  DrainQueue(slot.regions[static_cast<size_t>(region)]);
}

void Scheduler::DrainQueue(EventQueue& queue) {
  while (!queue.empty()) {
    Event* event = queue.Pop();
    if (event->callback) {
      event->callback();
    }
    pool_.Release(event);
  }
}

}  // namespace delta
