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

TEST(NetResolution, TriregRetainsPrevValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();

  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NetResolution, TriregDrivenNormally) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ChargeDecay, DecayChangesValueToX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

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

TEST(ChargeDecay, DecayCancelledWhenDriverReturns) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 100;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 99);
  net.Resolve(arena, &sched);

  sched.Run();
  EXPECT_EQ(var->value.ToUint64(), 99u);
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

}  // namespace
