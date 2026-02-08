#include <gtest/gtest.h>

#include "simulation/process.h"

using namespace delta;

TEST(Process, PromiseTypeMethods) {
  SimCoroutine::promise_type promise;

  auto coro = promise.get_return_object();
  EXPECT_FALSE(coro.done());

  auto init = promise.initial_suspend();
  (void)init;

  promise.return_void();
  promise.unhandled_exception();

  auto fin = promise.final_suspend();
  (void)fin;
}

TEST(Process, MoveSemantics) {
  SimCoroutine::promise_type promise;
  auto a = promise.get_return_object();
  EXPECT_FALSE(a.done());

  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.done());
  EXPECT_TRUE(a.done());  // NOLINT -- moved-from state check
}
