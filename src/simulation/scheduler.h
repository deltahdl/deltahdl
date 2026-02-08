#pragma once

#include "common/types.h"

#include <array>
#include <cstdint>
#include <functional>
#include <map>

namespace delta {

// --- Event types for the stratified scheduler ---

enum class EventKind : uint8_t {
    Update,
    Evaluation,
};

struct Event {
    EventKind kind = EventKind::Evaluation;
    void* target = nullptr;
    std::function<void()> callback;
    Event* next = nullptr;
};

// --- Intrusive linked-list event queue ---

struct EventQueue {
    Event* head = nullptr;
    Event* tail = nullptr;

    void push(Event* event);
    Event* pop();
    bool empty() const { return head == nullptr; }
    void clear();
};

// --- Time slot: one queue per region ---

struct TimeSlot {
    std::array<EventQueue, kRegionCount> regions{};

    bool any_nonempty() const;
    bool any_nonempty_in(Region first, Region last) const;
};

// --- Stratified event scheduler (IEEE 1800-2023 section 4.5) ---

class Scheduler {
  public:
    Scheduler() = default;

    SimTime current_time() const { return current_time_; }
    bool has_events() const { return !event_calendar_.empty(); }

    void schedule_event(SimTime time, Region region, Event* event);
    void run();

  private:
    void execute_time_slot(TimeSlot& slot);
    void execute_active_regions(TimeSlot& slot);
    void execute_reactive_regions(TimeSlot& slot);
    void execute_region(EventQueue& queue);

    bool iterate_active_set(TimeSlot& slot);
    bool iterate_reactive_set(TimeSlot& slot);

    std::map<SimTime, TimeSlot> event_calendar_;
    SimTime current_time_{0};
    bool stop_requested_ = false;
};

} // namespace delta
