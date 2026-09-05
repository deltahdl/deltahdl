#pragma once

#include <cstdint>

namespace delta {

// What executing a statement did, as its caller needs to know it: whether the
// statement finished, or whether control left it for somewhere the caller has
// to take it.
//
// Suspending is not one of these. A statement that waits -- a delay, an event
// control, a wait -- is a coroutine that co_awaits an awaiter and resumes
// where it left off, so it reports kDone when it eventually finishes and the
// caller never sees the suspension at all. ExecDelay in
// stmt_exec_control.cpp is the shape: `co_await DelayAwaiter{ctx, ticks}` and
// then `co_return StmtResult::kDone`.
//
// kSuspendDelay and kSuspendEvent stood here until they were removed. They
// were written in 15cb235f0, before there were coroutines, when the executor
// answered a kDelay or a kEventControl by returning "this statement
// suspended" and leaving the caller to arrange the rest. Nothing has returned
// either since the coroutine executor replaced that, and nothing tested for
// either, so every `result != StmtResult::kDone` in the tree silently counted
// two values no statement could produce among the ones that mean control went
// somewhere.
enum class StmtResult : uint8_t {
  kDone,
  kBreak,
  kContinue,
  kReturn,
  kDisable,
};

}  // namespace delta
