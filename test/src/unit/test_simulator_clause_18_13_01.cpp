#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, UrandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// "The number shall be unsigned."
TEST(SysTask, UrandomReturnsUnsigned) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

// The same seed shall replay the same sequence of random numbers.
TEST(SysTask, UrandomSameSeedReplaysSequence) {
  SysTaskFixture f;
  auto* seeded = MkSysCall(f.arena, "$urandom", {MkInt(f.arena, 12345)});
  auto* plain = MkSysCall(f.arena, "$urandom", {});

  uint32_t a0 =
      static_cast<uint32_t>(EvalExpr(seeded, f.ctx, f.arena).ToUint64());
  uint32_t a1 =
      static_cast<uint32_t>(EvalExpr(plain, f.ctx, f.arena).ToUint64());
  uint32_t a2 =
      static_cast<uint32_t>(EvalExpr(plain, f.ctx, f.arena).ToUint64());

  // Re-seeding with the same value restarts the identical sequence.
  uint32_t b0 =
      static_cast<uint32_t>(EvalExpr(seeded, f.ctx, f.arena).ToUint64());
  uint32_t b1 =
      static_cast<uint32_t>(EvalExpr(plain, f.ctx, f.arena).ToUint64());
  uint32_t b2 =
      static_cast<uint32_t>(EvalExpr(plain, f.ctx, f.arena).ToUint64());

  EXPECT_EQ(a0, b0);
  EXPECT_EQ(a1, b1);
  EXPECT_EQ(a2, b2);
}

// "a new 32-bit random number each time it is called": the generator advances
// per call, so successive draws are not the same value.
TEST(SysTask, UrandomAdvancesEachCall) {
  SysTaskFixture f;
  auto* call = MkSysCall(f.arena, "$urandom", {});
  uint32_t first =
      static_cast<uint32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
  uint32_t second =
      static_cast<uint32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
  EXPECT_NE(first, second);
}

// The RNG is deterministic: two fresh contexts replay the same sequence from
// the start without any explicit seed.
TEST(SysTask, UrandomDeterministicAcrossContexts) {
  SysTaskFixture f1;
  SysTaskFixture f2;
  uint32_t a = static_cast<uint32_t>(
      EvalExpr(MkSysCall(f1.arena, "$urandom", {}), f1.ctx, f1.arena)
          .ToUint64());
  uint32_t b = static_cast<uint32_t>(
      EvalExpr(MkSysCall(f2.arena, "$urandom", {}), f2.ctx, f2.arena)
          .ToUint64());
  EXPECT_EQ(a, b);
}

// The seed argument determines the sequence: distinct seeds diverge.
TEST(SysTask, UrandomSeedSelectsSequence) {
  SysTaskFixture f;
  uint32_t s1 = static_cast<uint32_t>(
      EvalExpr(MkSysCall(f.arena, "$urandom", {MkInt(f.arena, 1)}), f.ctx,
               f.arena)
          .ToUint64());
  uint32_t s2 = static_cast<uint32_t>(
      EvalExpr(MkSysCall(f.arena, "$urandom", {MkInt(f.arena, 2)}), f.ctx,
               f.arena)
          .ToUint64());
  EXPECT_NE(s1, s2);
}

// Edge case: the seed may be any integral expression, including a value wider
// than 32 bits; it is accepted and seeds deterministically.
TEST(SysTask, UrandomWideSeedAcceptedAndReplays) {
  SysTaskFixture f;
  auto* wide = MkSysCall(f.arena, "$urandom",
                         {MkInt(f.arena, 0x1234'5678'9abc'def0ull)});
  uint32_t first =
      static_cast<uint32_t>(EvalExpr(wide, f.ctx, f.arena).ToUint64());
  uint32_t again =
      static_cast<uint32_t>(EvalExpr(wide, f.ctx, f.arena).ToUint64());
  EXPECT_EQ(first, again);
}

}  // namespace
