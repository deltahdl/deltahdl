#include <catch2/catch_test_macros.hpp>

#include "common/types.h"
#include "sim/scheduler.h"

using namespace delta;

TEST_CASE("Scheduler initial state", "[scheduler]") {
    Scheduler sched;
    REQUIRE_FALSE(sched.has_events());
    REQUIRE(sched.current_time().ticks == 0);
}

TEST_CASE("Scheduler schedule and run single event", "[scheduler]") {
    Scheduler sched;
    bool executed = false;
    Event ev;
    ev.kind = EventKind::Evaluation;
    ev.callback = [&executed]() { executed = true; };
    sched.schedule_event({0}, Region::Active, &ev);
    REQUIRE(sched.has_events());
    sched.run();
    REQUIRE(executed);
}

TEST_CASE("Scheduler time ordering", "[scheduler]") {
    Scheduler sched;
    std::vector<int> order;

    Event ev1;
    ev1.kind = EventKind::Evaluation;
    ev1.callback = [&order]() { order.push_back(1); };

    Event ev2;
    ev2.kind = EventKind::Evaluation;
    ev2.callback = [&order]() { order.push_back(2); };

    sched.schedule_event({10}, Region::Active, &ev2);
    sched.schedule_event({5}, Region::Active, &ev1);

    sched.run();
    REQUIRE(order.size() == 2);
    REQUIRE(order[0] == 1); // time 5 first
    REQUIRE(order[1] == 2); // time 10 second
}

TEST_CASE("Scheduler region ordering within time slot", "[scheduler]") {
    Scheduler sched;
    std::vector<int> order;

    Event ev_active;
    ev_active.kind = EventKind::Evaluation;
    ev_active.callback = [&order]() { order.push_back(1); };

    Event ev_nba;
    ev_nba.kind = EventKind::Evaluation;
    ev_nba.callback = [&order]() { order.push_back(2); };

    // Schedule NBA before Active, but Active should execute first
    sched.schedule_event({0}, Region::NBA, &ev_nba);
    sched.schedule_event({0}, Region::Active, &ev_active);

    sched.run();
    REQUIRE(order.size() == 2);
    REQUIRE(order[0] == 1); // Active first
    REQUIRE(order[1] == 2); // NBA second
}
