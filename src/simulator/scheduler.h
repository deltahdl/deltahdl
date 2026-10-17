#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

class SimContext;
struct Process;

enum class EventKind : uint8_t {
  kUpdate,
  kEvaluation,
  kPli,
};

struct Event {
  EventKind kind = EventKind::kEvaluation;
  void* target = nullptr;
  std::function<void()> callback;
  Event* next = nullptr;
  // When set and pointing at a true value, this event has been superseded and
  // does no work (an inertial-delay timeout an operand change cancelled, IEEE
  // 1800 §28). Such an event must not advance simulation time. Null for every
  // ordinary event, which is always live.
  std::shared_ptr<bool> superseded = nullptr;
};

struct EventQueue {
  Event* head = nullptr;
  Event* tail = nullptr;

  void Push(Event* event);
  Event* Pop();
  bool empty() const { return head == nullptr; }
  void Clear();
};

// §37.81: a time whose time slot still holds events, and whether one of them
// stands in a region before the Postponed region, where cbReadOnlySynch runs
// (§4.10, Table 4-1).
struct PendingTimeSlot {
  SimTime time;
  bool before_read_only_synch = false;
};

struct TimeSlot {
  std::array<EventQueue, kRegionCount> regions{};

  bool AnyNonemptyIn(Region first, Region last) const;

  // Lowest-ordinal region in [first, last] holding an event, or kCOUNT when the
  // whole range is empty. Drives the §4.5 earliest-nonempty-first iteration.
  Region FirstNonemptyIn(Region first, Region last) const;

  bool AnyIterativeNonempty() const;
};

class Arena;

class EventPool {
 public:
  explicit EventPool(Arena& arena) : arena_(arena) {}

  Event* Acquire();

  void Release(Event* event);

  size_t FreeCount() const { return free_count_; }

 private:
  Arena& arena_;
  Event* free_list_ = nullptr;
  size_t free_count_ = 0;
};

class Scheduler {
 public:
  explicit Scheduler(Arena& arena) : pool_(arena) {}

  SimTime CurrentTime() const { return current_time_; }

  // The time of the earliest event still scheduled - the next future event.
  // When nothing remains queued there is no future event, so the current time
  // is reported instead. Events at or before current_time_ are skipped: while
  // the current time slot is being drained its entry is still present, and a
  // query for the next event (e.g. §38.13 time-queue) must report only future
  // work.
  SimTime NextEventTime() const {
    if (event_calendar_.empty()) return current_time_;
    auto it = event_calendar_.upper_bound(current_time_);
    if (it == event_calendar_.end()) return current_time_;
    return it->first;
  }

  // §37.44: record that the run has switched to `proc`, and hand back the
  // threads it has switched to so far, in that order. A thread is a
  // SystemVerilog process, an always procedure or a fork branch for instance,
  // and a switch to one is where a process becomes that: a process
  // this has never seen is one the run never reached. SimContext::
  // SetCurrentProcess is the one place every resume passes through and is what
  // calls this; VpiContext::RefreshThreadObjects reads the list back.
  void NoteThreadSwitch(Process* proc) {
    if (proc == nullptr) return;
    if (threads_seen_.insert(proc).second) threads_.push_back(proc);
  }
  const std::vector<Process*>& Threads() const { return threads_; }

  // §8.29: a process made with stacks of its own before it first runs -- a
  // fork branch carrying its parent's locals, an embedded covergroup's
  // sampling process carrying its object -- whose stacks the class garbage
  // collector reads as roots alongside those of the threads above.
  void NoteCarrier(Process* proc) { carriers_.push_back(proc); }
  const std::vector<Process*>& Carriers() const { return carriers_; }

  // §8.29: the class handles a scheduled assignment carries in a value until it
  // runs, counted per handle, which the class garbage collector reads as roots
  // (PinClassHandles in class_gc_roots.h).
  void PinHandle(uint64_t handle) { ++pinned_handles_[handle]; }
  void UnpinHandle(uint64_t handle) {
    auto it = pinned_handles_.find(handle);
    if (it != pinned_handles_.end() && --it->second == 0) {
      pinned_handles_.erase(it);
    }
  }
  const std::map<uint64_t, uint32_t>& PinnedHandles() const {
    return pinned_handles_;
  }

  // §8.29: when the class garbage collector runs during a run -- at the end of
  // a time slot, once as many objects have been made since its last pass as
  // that pass left live, and at least one. The work it does is then
  // proportional to the objects the run makes.
  void NoteClassObjectMade() { ++class_objects_made_; }
  void NoteClassCollection(size_t live) {
    class_objects_made_ = 0;
    class_collection_due_at_ = live > 0 ? live : 1;
  }
  bool ClassCollectionDue() const {
    return class_objects_made_ >= class_collection_due_at_;
  }

  Region CurrentRegion() const { return current_region_; }
  bool HasEvents() const { return !event_calendar_.empty(); }
  // §37.81: the time slots still holding events, in increasing time.
  std::vector<PendingTimeSlot> PendingTimeSlots() const;

  // Back-reference to the owning context, set once at construction. Used to
  // clear the executing process when the scheduler goes idle (see Run()) and
  // to run the final procedures (see EndSimulation()).
  void SetContext(SimContext* ctx) { ctx_ = ctx; }

  void ScheduleEvent(SimTime time, Region region, Event* event);
  // §10.4.2 with §9.4.5: a nonblocking assignment whose update an intra-
  // assignment event control defers resolves its target where it executes,
  // and the updates that resolution makes wait for the event. While a capture
  // is set, every event scheduled is held in it, with its region, rather than
  // queued; the deferring statement queues them once the event has occurred.
  using NbaCapture = std::vector<std::pair<Event*, Region>>;
  void SetNbaCapture(NbaCapture* capture) { nba_capture_ = capture; }
  void Run();
  // §9.2.3 with §38.36.3: ends a simulation whose event loop Run() has ended,
  // by the event queue running empty or by a $finish: the final procedures
  // run, and then the cbEndOfSimulation callbacks, which §9.2.3 puts after
  // them.
  void EndSimulation();

  EventPool& GetEventPool() { return pool_; }

  // Registers work to run once a time slot has finished, after its Postponed
  // region. A time slot ends once but several unrelated readers have something
  // to do at that point, and a single stored callback silently replaced
  // whichever had registered before, so the callbacks are held as a list and
  // each runs in registration order.
  void AddPostTimestepCallback(std::function<void()> cb) {
    post_timestep_cbs_.push_back(std::move(cb));
  }

  // Registers work to run as each time slot begins, once its Preponed region
  // has sampled it and before its Pre-Active region; the callbacks run in
  // registration order.
  void AddTimeSlotStartCallback(std::function<void()> cb) {
    time_slot_start_cbs_.push_back(std::move(cb));
  }

  size_t IllegalPreponedScheduleCount() const {
    return illegal_preponed_schedule_count_;
  }

  size_t IllegalPreponedWriteCount() const {
    return illegal_preponed_write_count_;
  }

  size_t IllegalPostponedScheduleCount() const {
    return illegal_postponed_schedule_count_;
  }

  size_t IllegalPostponedWriteCount() const {
    return illegal_postponed_write_count_;
  }

  size_t IllegalObservedPliCount() const { return illegal_observed_pli_count_; }

  // §4.4.3.5: the Pre-Observed region is read-only - it is illegal to schedule
  // an event into the current time slot or to write a net or variable from
  // within it. Each violation attempt is tallied here.
  size_t IllegalPreObservedScheduleCount() const {
    return illegal_pre_observed_schedule_count_;
  }

  size_t IllegalPreObservedWriteCount() const {
    return illegal_pre_observed_write_count_;
  }

  size_t UpdateEventScheduledCount() const {
    return update_events_scheduled_count_;
  }

  size_t EvaluationEventScheduledCount() const {
    return evaluation_events_scheduled_count_;
  }

  void NoteWriteAttempt() {
    if (current_region_ == Region::kPreponed) {
      ++illegal_preponed_write_count_;
    } else if (current_region_ == Region::kPostponed) {
      ++illegal_postponed_write_count_;
    } else if (current_region_ == Region::kPreObserved) {
      ++illegal_pre_observed_write_count_;
    }
  }

  static bool IsAnyOrderRegion(Region r) {
    return r == Region::kActive || r == Region::kReactive;
  }

  static constexpr bool AllowsUserOrderControl() { return false; }

  void NoteMidStatementSuspension() { ++mid_statement_suspension_count_; }
  size_t MidStatementSuspensionCount() const {
    return mid_statement_suspension_count_;
  }

  static constexpr Region HomeRegionForReactiveBlockingAssign() {
    return Region::kReactive;
  }

  static constexpr Region ReactiveSetDualOf(Region active) {
    switch (active) {
      case Region::kActive:
        return Region::kReactive;
      case Region::kInactive:
        return Region::kReInactive;
      case Region::kNBA:
        return Region::kReNBA;
      default:
        return Region::kCOUNT;
    }
  }

 private:
  // §20.2: whether an explicit $finish, $stop or $fatal has ended the run,
  // after which no scheduled event runs, in the current time slot or a later
  // one. A scheduler with no context is never halted.
  bool Halted() const;
  // §24.3: whether every initial procedure of every program has ended, which
  // ends the run once the current time slot is done.
  bool ProgramsEnded() const;
  // Returns every event still queued in `slot` to the pool without running it.
  void ReleaseSlot(TimeSlot& slot);
  void ExecuteTimeSlot(TimeSlot& slot);
  void ExecuteRegion(TimeSlot& slot, Region region);
  void DrainQueue(EventQueue& queue);
  // Calls `event` and gives it back to the pool.
  void RunEvent(Event* event);
  // Executes `region` of an iterative loop whose home region is `home`
  // (scheduler.cpp).
  void ExecuteIterativeRegion(TimeSlot& slot, Region region, Region home);

  bool IterateActiveSet(TimeSlot& slot);
  bool IterateReactiveSet(TimeSlot& slot);

  EventPool pool_;
  SimContext* ctx_ = nullptr;
  std::map<SimTime, TimeSlot> event_calendar_;
  std::vector<std::function<void()>> post_timestep_cbs_;
  std::vector<std::function<void()>> time_slot_start_cbs_;
  // §37.44: the processes the run has switched to, in order, and the set that
  // keeps that order free of repeats -- a process is switched to once per
  // resume and is one thread however many times it runs.
  std::vector<Process*> threads_;
  std::unordered_set<Process*> threads_seen_;
  std::vector<Process*> carriers_;
  std::map<uint64_t, uint32_t> pinned_handles_;
  size_t class_objects_made_ = 0;
  size_t class_collection_due_at_ = 1;

  SimTime current_time_{0};
  Region current_region_ = Region::kCOUNT;
  size_t illegal_preponed_schedule_count_ = 0;
  size_t illegal_preponed_write_count_ = 0;
  size_t illegal_postponed_schedule_count_ = 0;
  size_t illegal_postponed_write_count_ = 0;
  size_t illegal_observed_pli_count_ = 0;
  size_t illegal_pre_observed_schedule_count_ = 0;
  size_t illegal_pre_observed_write_count_ = 0;
  size_t update_events_scheduled_count_ = 0;
  size_t evaluation_events_scheduled_count_ = 0;
  size_t mid_statement_suspension_count_ = 0;
  bool stop_requested_ = false;
  NbaCapture* nba_capture_ = nullptr;
};

}  // namespace delta
