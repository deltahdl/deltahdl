#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, UrandomRangeInBounds) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 10), MkInt(f.arena, 5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  uint64_t val = result.ToUint64();
  EXPECT_GE(val, 5u);
  EXPECT_LE(val, 10u);
}

// "If minval is omitted, the function shall return a value in the range of
// maxval ... 0." The single-argument form must yield a value bounded by zero.
TEST(SysTask, UrandomRangeOmittedMinvalIsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range", {MkInt(f.arena, 7)});
  for (int i = 0; i < 200; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v > 7u) FAIL() << "value " << v << " exceeds maxval 7";
  }
}

// "All of the three previous examples produce a value in the range of 0 to 7,
// inclusive." Example 3 passes the bounds reversed, exercising the automatic
// argument swap.
TEST(SysTask, UrandomRangeReversedBoundsAreSwapped) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 0), MkInt(f.arena, 7)});
  for (int i = 0; i < 200; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v > 7u) FAIL() << "value " << v << " exceeds the upper bound";
  }
}

// Edge case for the range claim: when maxval and minval coincide, the
// half-open interval collapses and the only legal return value is the shared
// boundary itself.
TEST(SysTask, UrandomRangeEqualBoundsReturnsBoundary) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 5), MkInt(f.arena, 5)});
  for (int i = 0; i < 50; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v != 5u) FAIL() << "value " << v << " is outside the degenerate range";
  }
}

// Edge case for the default-minval rule: a single-argument call with maxval=0
// reduces to the degenerate [0,0] range, so the only legal return value is 0.
TEST(SysTask, UrandomRangeZeroMaxvalReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range", {MkInt(f.arena, 0)});
  for (int i = 0; i < 50; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v != 0u) FAIL() << "value " << v << " is outside the [0,0] range";
  }
}

// "$urandom_range() is automatically thread stable (see 18.14.2)." Forked
// children draw from independent, hierarchically seeded RNGs, so a second
// run of the same program with the same parent state replays identical
// per-thread values regardless of the scheduler's interleaving.
TEST(SysTask, UrandomRangeIsThreadStable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    SimFixtureSeeded f;
    auto* design = ElaborateSrc(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      a = $urandom_range(1000000);\n"
        "      b = $urandom_range(1000000);\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        f);
    ASSERT_NE(design, nullptr);
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
    a = f.ctx.FindVariable("a")->value.ToUint64();
    b = f.ctx.FindVariable("b")->value.ToUint64();
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

}  // namespace
