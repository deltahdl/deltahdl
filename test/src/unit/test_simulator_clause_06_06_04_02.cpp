#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

static Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = ~uint64_t{0};
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}

namespace {

TEST(ChargeDecay, NoDecayWhenDecayTicksZero) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 0;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ChargeDecay, NoDecayScheduledWithoutScheduler) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;
  net.drivers.push_back(MakeAllZ(arena, 8));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ChargeDecay, IdealCapacitiveRetainsValue) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xAB);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 0;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);

  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);

  EXPECT_FALSE(sched.HasEvents());
}

}  // namespace
