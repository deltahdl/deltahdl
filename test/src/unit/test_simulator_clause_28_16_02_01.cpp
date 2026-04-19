#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// All-z driver: every bit is (aval=1, bval=1) → z.
Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = ~uint64_t{0};
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}

// All-x driver: every bit is (aval=0, bval=1) → x.
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

// §28.16.2.1: Charge decay is the cause of transition of a stored 1 to x
// after the specified delay.
TEST(ChargeDecayProcess, StoredOneTransitionsToXAfterDelay) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xFF);  // stored 1s
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

// §28.16.2.1: Charge decay is the cause of transition of a stored 0 to x
// after the specified delay.
TEST(ChargeDecayProcess, StoredZeroTransitionsToXAfterDelay) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);  // stored 0s
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

// §28.16.2.1: Process begins when drivers transition from driving to off —
// the simulator must schedule a decay event at that moment, and not before.
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

// §28.16.2.1 (b): Process ends when drivers turn on and propagate 1;
// the pending decay does not fire.
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

// §28.16.2.1 (b): Process ends when drivers turn on and propagate 0.
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

// §28.16.2.1 (b): Process ends when drivers turn on and propagate x —
// the driver-on path must handle x the same as 0 or 1.
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

// §28.16.2.1: Both 1-bits and 0-bits in the same stored value must
// transition to x in a single decay event — the "1 or 0" in the LRM
// applies per-bit, so a mixed vector decays uniformly.
TEST(ChargeDecayProcess, MixedStoredValueDecaysAllBitsToX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xA5);  // alternating 1s and 0s
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 35;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// §28.16.2.1: Decay applies across the full width of the stored value —
// a multi-word vector must decay in every word, not just the first.
TEST(ChargeDecayProcess, WideVectorDecaysEveryWord) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 128, 0);
  // Set both words to known 1s by flipping aval (bval already 0 → known).
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

// §28.16.2.1: A second driver-off after a (b)-ended decay must restart the
// process from scratch — pins req (2) applied more than once and guards
// against stale-state bugs where a cancelled decay prevents a new one.
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
