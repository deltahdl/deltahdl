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

// §6.6.4.2: in the ideal capacitive state the trireg holds its last driven
// value exactly, independent of what that value is. A value that already
// contains unknown (x) and high-impedance (z) bits must be retained verbatim;
// the ideal state never forces any retained bit to x (that only happens on
// charge decay, which is disabled when the decay time is zero).
TEST(ChargeDecay, IdealStatePreservesUnknownBits) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  // Low nibble encodes, from bit 0 up: 0, 1, x, z (a mix of known and
  // unknown bits); the high nibble is all known zeros.
  auto val = MakeLogic4Vec(arena, 8);
  val.words[0].aval = 0b1010;
  val.words[0].bval = 0b1100;
  var->value = val;
  const uint64_t kExpectedAval = val.words[0].aval;
  const uint64_t kExpectedBval = val.words[0].bval;

  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 0;
  net.drivers.push_back(MakeAllZ(arena, 8));

  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.words[0].aval, kExpectedAval);
  EXPECT_EQ(var->value.words[0].bval, kExpectedBval);

  net.Resolve(arena, &sched);
  EXPECT_EQ(var->value.words[0].aval, kExpectedAval);
  EXPECT_EQ(var->value.words[0].bval, kExpectedBval);

  EXPECT_FALSE(sched.HasEvents());
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
