#include <gtest/gtest.h>

#include <cstdint>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_fork_urandom_programs.h"
#include "helpers_seeded_run.h"
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

TEST(SysTask, UrandomRangeOmittedMinvalIsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range", {MkInt(f.arena, 7)});
  for (int i = 0; i < 200; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v > 7u) FAIL() << "value " << v << " exceeds maxval 7";
  }
}

TEST(SysTask, UrandomRangeEqualBoundsReturnsBoundary) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 5), MkInt(f.arena, 5)});
  for (int i = 0; i < 50; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v != 5u) FAIL() << "value " << v << " is outside the degenerate range";
  }
}

TEST(SysTask, UrandomRangeZeroMaxvalReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range", {MkInt(f.arena, 0)});
  for (int i = 0; i < 50; ++i) {
    uint64_t v = EvalExpr(expr, f.ctx, f.arena).ToUint64();
    if (v != 0u) FAIL() << "value " << v << " is outside the [0,0] range";
  }
}

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

TEST(SysTask, UrandomRangeIsThreadStable) {
  ExpectForkedUrandomRangeDrawsReplay();
}

}  // namespace
