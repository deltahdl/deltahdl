#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_seeded_run.h"
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

// "If maxval is less than minval, the arguments are automatically reversed."
// Driven from real source through the full pipeline with runtime (non-literal)
// operands: maxval=hi=5 is passed smaller than minval=lo=20, so the effective
// range must widen to [5,20] rather than collapsing. Every draw stays inside
// [5,20] (outside stays zero) and some exceed the nominal maxval of 5 (wide is
// positive), proving the reversal actually took effect and the upper bound
// became 20.
TEST(SysTask, UrandomRangeReversedRuntimeBoundsWidenRange) {
  auto vals = RunSeededAndRead(
      "module t;\n"
      "  int unsigned lo;\n"
      "  int unsigned hi;\n"
      "  int unsigned r;\n"
      "  int unsigned outside;\n"
      "  int unsigned wide;\n"
      "  int i;\n"
      "  initial begin\n"
      "    lo = 20;\n"
      "    hi = 5;\n"
      "    outside = 0;\n"
      "    wide = 0;\n"
      "    for (i = 0; i < 300; i = i + 1) begin\n"
      "      r = $urandom_range(hi, lo);\n"
      "      if (r < 5 || r > 20) outside = outside + 1;\n"
      "      if (r > 5) wide = wide + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      {"outside", "wide"});
  EXPECT_EQ(vals[0], 0u);
  EXPECT_GT(vals[1], 0u);
}

// "The $urandom_range() function returns an unsigned integer within a
// specified range." The prototype types both arguments as int unsigned, so a
// range lying entirely above 2^31 must be honored: were either bound or the
// result treated as a signed int, the interval would appear inverted or the
// draw would fall outside it. Driven from real source with runtime operands
// whose values exceed INT_MAX, every draw stays within [3e9, 4e9].
TEST(SysTask, UrandomRangeUnsignedRangeAboveIntMax) {
  auto vals = RunSeededAndRead(
      "module t;\n"
      "  int unsigned lo;\n"
      "  int unsigned hi;\n"
      "  int unsigned r;\n"
      "  int unsigned outside;\n"
      "  int i;\n"
      "  initial begin\n"
      "    lo = 3000000000;\n"
      "    hi = 4000000000;\n"
      "    outside = 0;\n"
      "    for (i = 0; i < 300; i = i + 1) begin\n"
      "      r = $urandom_range(hi, lo);\n"
      "      if (r < 3000000000 || r > 4000000000) outside = outside + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      {"outside"});
  EXPECT_EQ(vals[0], 0u);
}

// "$urandom_range() is automatically thread stable (see 18.14.2)." Forked
// children draw from independent, hierarchically seeded RNGs, so a second
// run of the same program with the same parent state replays identical
// per-thread values regardless of the scheduler's interleaving.
TEST(SysTask, UrandomRangeIsThreadStable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
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
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

}  // namespace
