#include "simulation/scheduler.h"

#include <cassert>

namespace delta {

// --- EventQueue ---

void EventQueue::push(Event* event) {
    event->next = nullptr;
    if (tail) {
        tail->next = event;
    } else {
        head = event;
    }
    tail = event;
}

Event* EventQueue::pop() {
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

void EventQueue::clear() {
    head = nullptr;
    tail = nullptr;
}

// --- TimeSlot ---

bool TimeSlot::any_nonempty() const {
    for (size_t i = 0; i < kRegionCount; ++i) {
        if (!regions[i].empty()) {
            return true;
        }
    }
    return false;
}

bool TimeSlot::any_nonempty_in(Region first, Region last) const {
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

void Scheduler::schedule_event(SimTime time, Region region, Event* event) {
    assert(!(time < current_time_));
    auto idx = static_cast<size_t>(region);
    event_calendar_[time].regions[idx].push(event);
}

void Scheduler::run() {
    while (!event_calendar_.empty() && !stop_requested_) {
        auto it = event_calendar_.begin();
        current_time_ = it->first;
        execute_time_slot(it->second);
        event_calendar_.erase(it);
    }
}

// --- Scheduler: time slot execution (IEEE 1800-2023 section 4.5) ---

void Scheduler::execute_time_slot(TimeSlot& slot) {
    // Preponed region: read-only sampling
    execute_region(slot.regions[static_cast<size_t>(Region::Preponed)]);

    // Iterate Active region set until stable
    while (iterate_active_set(slot)) {
        // Keep iterating while events exist in active regions
    }

    // Iterate Reactive region set until stable
    while (iterate_reactive_set(slot)) {
        // Keep iterating while events exist in reactive regions
    }

    // Postponed region
    execute_region(slot.regions[static_cast<size_t>(Region::Postponed)]);
}

// --- Scheduler: Active region set iteration ---
// Regions: PreActive, Active, Inactive, PreNBA, NBA, PostNBA

bool Scheduler::iterate_active_set(TimeSlot& slot) {
    bool did_work = false;

    execute_active_regions(slot);
    if (slot.any_nonempty_in(Region::PreActive, Region::PostNBA)) {
        did_work = true;
    }

    // Drain all active-side regions in priority order
    while (slot.any_nonempty_in(Region::PreActive, Region::PostNBA)) {
        execute_active_regions(slot);
    }

    return did_work;
}

void Scheduler::execute_active_regions(TimeSlot& slot) {
    auto exec = [&](Region r) {
        execute_region(slot.regions[static_cast<size_t>(r)]);
    };

    exec(Region::PreActive);
    exec(Region::Active);
    exec(Region::Inactive);
    exec(Region::PreNBA);
    exec(Region::NBA);
    exec(Region::PostNBA);
}

// --- Scheduler: Reactive region set iteration ---
// Regions: PreObserved, Observed, PostObserved, Reactive,
//          ReInactive, PreReNBA, ReNBA, PostReNBA, PrePostponed

bool Scheduler::iterate_reactive_set(TimeSlot& slot) {
    bool did_work = false;

    execute_reactive_regions(slot);
    if (slot.any_nonempty_in(Region::PreObserved, Region::PrePostponed)) {
        did_work = true;
    }

    while (slot.any_nonempty_in(Region::PreObserved, Region::PrePostponed)) {
        execute_reactive_regions(slot);

        // If active-side events were generated, restart active set
        if (slot.any_nonempty_in(Region::PreActive, Region::PostNBA)) {
            while (iterate_active_set(slot)) {}
        }
    }

    return did_work;
}

void Scheduler::execute_reactive_regions(TimeSlot& slot) {
    auto exec = [&](Region r) {
        execute_region(slot.regions[static_cast<size_t>(r)]);
    };

    exec(Region::PreObserved);
    exec(Region::Observed);
    exec(Region::PostObserved);
    exec(Region::Reactive);
    exec(Region::ReInactive);
    exec(Region::PreReNBA);
    exec(Region::ReNBA);
    exec(Region::PostReNBA);
    exec(Region::PrePostponed);
}

// --- Scheduler: single region drain ---

void Scheduler::execute_region(EventQueue& queue) {
    while (!queue.empty()) {
        Event* event = queue.pop();
        if (event->callback) {
            event->callback();
        }
    }
}

} // namespace delta
