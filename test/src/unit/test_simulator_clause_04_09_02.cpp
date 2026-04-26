#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

// §4.9.2 atom: a procedural continuous `assign` corresponds to a process that
// is sensitive to the source elements in the expression. Observed by lowering
// `assign q = src;` in an initial block and changing `src` afterwards — the
// target tracks the new source value, which is only possible if
// `ExecForceOrAssignImpl` registered the assign as a process watching `src`.
TEST(ProceduralContinuousSchedulingSim, AssignCorrespondsToProcessSensitiveToSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    assign q = src;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 99u);
  EXPECT_TRUE(q->is_forced);
}

// §4.9.2 atom: a procedural continuous `force` likewise corresponds to a
// process sensitive to the source elements. Observed by `force q = src;` and
// then changing `src` — the production force path in `ExecForceOrAssignImpl`
// must have registered watchers on `src` for this to update.
TEST(ProceduralContinuousSchedulingSim, ForceCorrespondsToProcessSensitiveToSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    q = 8'd0;\n"
      "    force q = src;\n"
      "    #10 src = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 77u);
  EXPECT_TRUE(q->is_forced);
}

// §4.9.2 atom: when the expression value changes, the procedural continuous
// assignment causes an active update to the target using current values to
// determine it. Observed by `force q = a + b;` then changing only `a` — the
// new value of `q` must combine the new `a` with the unchanged-but-current
// `b`. A stale-snapshot implementation would yield the original sum.
TEST(ProceduralContinuousSchedulingSim, ExpressionChangeUsesCurrentValuesForTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    force q = a + b;\n"
      "    #10 a = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 24u);
}

// §4.9.2 atom: a `deassign` deactivates the corresponding procedural
// continuous `assign`. Observed by `assign q = src; deassign q;` then
// changing `src` — `q` must no longer track `src`, and the variable's
// `is_forced` flag must be cleared by `ExecReleaseOrDeassignImpl`.
TEST(ProceduralContinuousSchedulingSim, DeassignDeactivatesAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    assign q = src;\n"
      "    #10 deassign q;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);
  EXPECT_EQ(q->value.ToUint64(), 5u);
}

// §4.9.2 atoms 1 and 2 (assign edge case — plural "source elements" plus
// current-value semantics): a procedural `assign` whose RHS contains more
// than one source element is sensitive to every one of them, and on a change
// to any single element the active update reads the current values of the
// others. Observed by `assign c = a + b;` followed by changing only `a` —
// the post-change `c` must equal the new `a` plus the *current* `b`. A
// snapshot at assign time would yield the original sum; a single-element
// watcher would not refire when only `a` moved.
TEST(ProceduralContinuousSchedulingSim, AssignTracksCurrentValuesAcrossMultipleSources) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    assign c = a + b;\n"
      "    #10 a = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 50u);
  EXPECT_TRUE(c->is_forced);
}

// §4.9.2 atom: a `release` deactivates the corresponding procedural
// continuous `force`. Observed by `force q = src; release q;` then changing
// `src` — `q` must not track the post-release source change; the production
// release path must clear `is_forced` and break the watcher chain.
TEST(ProceduralContinuousSchedulingSim, ReleaseDeactivatesForce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    q = 8'd0;\n"
      "    force q = src;\n"
      "    #10 release q;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);
  EXPECT_EQ(q->value.ToUint64(), 5u);
}

