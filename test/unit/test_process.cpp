#include <catch2/catch_test_macros.hpp>

#include "simulation/process.h"

using namespace delta;

TEST_CASE("SimCoroutine promise_type methods", "[process]") {
  SimCoroutine::promise_type promise;

  auto coro = promise.get_return_object();
  REQUIRE_FALSE(coro.done());

  auto init = promise.initial_suspend();
  (void)init;

  promise.return_void();
  promise.unhandled_exception();

  auto fin = promise.final_suspend();
  (void)fin;
}

TEST_CASE("SimCoroutine move semantics", "[process]") {
  SimCoroutine::promise_type promise;
  auto a = promise.get_return_object();
  REQUIRE_FALSE(a.done());

  SimCoroutine b = std::move(a);
  REQUIRE_FALSE(b.done());
  REQUIRE(a.done());  // NOLINT — moved-from state check
}
