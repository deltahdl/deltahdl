#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = ~uint64_t{0};
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}

Logic4Vec MakeAllX(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = 0;
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}

bool AllBitsX(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != 0) return false;
    if (v.words[w].bval != ~uint64_t{0}) return false;
  }
  return true;
}

TEST(ChargeDecayProcess, StoredOneTransitionsToXAfterDelay) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xFF);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 40;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(ChargeDecayProcess, StoredZeroTransitionsToXAfterDelay) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 25;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_TRUE(AllBitsX(var->value));
}

TEST(ChargeDecayProcess, DecayFiresOnlyAfterChargeDecayTimeElapses) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xFF);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 42;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  // The transition to x happens when the charge decay time elapses, not at the
  // moment the drivers turn off: the decay event is queued exactly decay_ticks
  // in the future and the stored 1s are still intact until then.
  ASSERT_TRUE(sched.HasEvents());
  EXPECT_EQ(sched.NextEventTime().ticks, 42u);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);

  sched.Run();

  // Only once the delay has elapsed do the known bits decay to x.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(ChargeDecayProcess, ProcessBeginsWhenDriversTurnOff) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0x33);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 20;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x33));
  net.Resolve(arena, &sched);
  ASSERT_FALSE(sched.HasEvents());

  net.drivers[0] = MakeAllZ(arena, 8);
  net.Resolve(arena, &sched);
  EXPECT_TRUE(sched.HasEvents());
}

TEST(ChargeDecayProcess, EndsWhenDriverPropagatesOne) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0x10);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 0x01);
  net.Resolve(arena, &sched);

  sched.Run();
  EXPECT_EQ(var->value.ToUint64(), 0x01u);
}

TEST(ChargeDecayProcess, EndsWhenDriverPropagatesZero) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xAA);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 0);
  net.Resolve(arena, &sched);

  sched.Run();
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ChargeDecayProcess, EndsWhenDriverPropagatesX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0x0F);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeAllX(arena, 8);
  net.Resolve(arena, &sched);

  sched.Run();
  EXPECT_TRUE(AllBitsX(var->value));
}

TEST(ChargeDecayProcess, WideVectorDecaysEveryWord) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 128, 0);

  var->value.words[0].aval = ~uint64_t{0};
  var->value.words[1].aval = ~uint64_t{0};
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 45;
  net.drivers.push_back(MakeAllZ(arena, 128));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_TRUE(AllBitsX(var->value));
}

TEST(ChargeDecayProcess, OnlyKnownBitsTransitionToX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);

  var->value.words[0].aval = 0b01010101;
  var->value.words[0].bval = 0b11001100;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 30;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0b01000100u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(ChargeDecayProcess, ReBeginsAfterDriverCyclesOffAgain) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0x10);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 0x77);
  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.ToUint64(), 0x77u);

  net.drivers[0] = MakeAllZ(arena, 8);
  net.Resolve(arena, &sched);

  sched.Run();
  EXPECT_TRUE(AllBitsX(var->value));
}

}  // namespace
