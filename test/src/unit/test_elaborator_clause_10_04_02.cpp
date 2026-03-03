// §10.4.2: Nonblocking procedural assignments

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, NbaDefersUpdate) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x <= 42;\n"
      "    x = x;  // read x: should still be 0 (X→0), not 42\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // NBA update deferred, but scheduler drains NBA after Active,
  // so after Run() completes the NBA has been applied.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x was read as 0 (from X init), then NBA applied 42.
  // The blocking assign `x = x` reads 0 and writes 0.
  // Then NBA applies 42. Final value: 42.
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, NbaAppliesToValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a <= 10;\n"
      "    b <= 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

// ---------------------------------------------------------------------------
// §10.4.2: Simple nonblocking assignment — value updates after scheduler run.
// ---------------------------------------------------------------------------
TEST(SimCh10b, SimpleNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a <= 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA does NOT take effect immediately — uses NBA region scheduling.
// The RHS is sampled in the Active region but the LHS update is deferred.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBADeferredUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    a <= 20;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  // b captures a's value before the NBA takes effect.
  EXPECT_EQ(b->value.ToUint64(), 10u);
  // a is updated in the NBA region.
  EXPECT_EQ(a->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// §10.4.2: Multiple NBAs to same variable — last one wins in NBA region.
// ---------------------------------------------------------------------------
TEST(SimCh10b, MultipleNBASameVarLastWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    a <= 2;\n"
      "    a <= 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA swap pattern — a <= b; b <= a; both capture old values.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBASwapPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  // Both RHS values are sampled before either NBA takes effect.
  EXPECT_EQ(a->value.ToUint64(), 20u);
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with expression on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAExpressionRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 7;\n"
      "    b <= a + 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bit-select on LHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBABitSelectLHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'b0000_0000;\n"
      "    a[3] <= 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  // Bit 3 set: 0000_1000 = 8.
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

}  // namespace
