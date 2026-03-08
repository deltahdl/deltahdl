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

// §6.6.4.2: Charge decays to X after decay_ticks elapse.
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

// §6.6.4.2: Ideal capacitive state — no decay when decay_ticks is zero.
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

// §6.6.4.2: Decay cancelled when drivers turn back on.
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

// §6.6.4.2: No decay scheduled when no scheduler is provided.
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

// §6.6.4.2: Charge decay from value 0 transitions to X.
TEST(ChargeDecay, DecayFromZeroToX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 30;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// §6.6.4.2: Multiple decay cycles — decay starts, is cancelled, then restarts.
TEST(ChargeDecay, MultipleCyclesDecayCancelRestart) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 10);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;

  // First cycle: drivers go Z, decay is scheduled.
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  // Driver returns — cancels first decay.
  net.drivers[0] = MakeLogic4VecVal(arena, 8, 77);
  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 77u);

  // Second cycle: drivers go Z again, new decay is scheduled.
  net.drivers[0] = MakeAllZ(arena, 8);
  net.Resolve(arena, &sched);

  // Run scheduler — only the second decay fires.
  sched.Run();
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// §6.6.4.2: Ideal capacitive state — trireg retains value indefinitely.
TEST(ChargeDecay, IdealCapacitiveRetainsValue) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xAB);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 0;

  // Multiple resolves with all-Z drivers — value never changes.
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);

  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);

  EXPECT_FALSE(sched.HasEvents());
}

}  // namespace
