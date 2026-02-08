#pragma once

#include "common/types.h"

#include <coroutine>
#include <cstdint>
#include <exception>

namespace delta {

// --- Coroutine return type for simulation processes ---

struct SimCoroutine {
    struct promise_type {
        SimCoroutine get_return_object() {
            auto handle = std::coroutine_handle<promise_type>::from_promise(*this);
            return SimCoroutine{handle};
        }

        std::suspend_always initial_suspend() noexcept { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        void return_void() {}
        void unhandled_exception() { exception = std::current_exception(); }

        std::exception_ptr exception = nullptr;
    };

    using handle_type = std::coroutine_handle<promise_type>;

    explicit SimCoroutine(handle_type h) : handle(h) {}

    SimCoroutine(const SimCoroutine&) = delete;
    SimCoroutine& operator=(const SimCoroutine&) = delete;

    SimCoroutine(SimCoroutine&& other) noexcept : handle(other.handle) { other.handle = nullptr; }

    SimCoroutine& operator=(SimCoroutine&& other) noexcept {
        if (this != &other) {
            destroy();
            handle = other.handle;
            other.handle = nullptr;
        }
        return *this;
    }

    ~SimCoroutine() { destroy(); }

    bool done() const { return !handle || handle.done(); }

    void resume() {
        if (handle && !handle.done()) {
            handle.resume();
        }
    }

    handle_type handle = nullptr;

  private:
    void destroy() {
        if (handle) {
            handle.destroy();
            handle = nullptr;
        }
    }
};

// --- Process handle alias ---

using ProcessHandle = std::coroutine_handle<SimCoroutine::promise_type>;

// --- Process kinds matching SystemVerilog constructs ---

enum class ProcessKind : uint8_t {
    Initial,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFF,
    Final,
    ContAssign,
};

// --- Process: a schedulable simulation process ---

struct Process {
    ProcessKind kind = ProcessKind::Initial;
    ProcessHandle coro = nullptr;
    Region home_region = Region::Active;
    uint32_t id = 0;
    bool active = true;

    bool done() const { return !coro || coro.done(); }

    void resume() {
        if (coro && !coro.done()) {
            coro.resume();
        }
    }
};

} // namespace delta
