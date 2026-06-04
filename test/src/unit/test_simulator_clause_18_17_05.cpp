#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborate, lower, and run a module, then read back a scalar variable as an
// unsigned value. The rand join tests gather statistics across many runs of a
// randsequence wrapped in a repeat loop, so they read counters left behind in
// module level variables.
uint64_t RunAndRead(const char* src, const char* var_name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  return var ? var->value.ToUint64() : 0;
}

// 18.17.5: rand join generates every operand sequence. With two single
// production operands their side effects both run regardless of interleaving
// order.
TEST(RandsequenceSim, RandJoinBothExecute) {
  uint64_t x = RunAndRead(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : rand join a b;\n"
      "      a : { x = x + 8'd10; };\n"
      "      b : { x = x + 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(x, 30u);
}

// 18.17.5: the relative order of the productions inside each interleaved
// sequence is always preserved. Across many runs `a` precedes `b` and `c`
// precedes `d` without exception.
TEST(RandsequenceSim, RandJoinPreservesRelativeOrder) {
  uint64_t viol = RunAndRead(
      "module t;\n"
      "  int pa, pb, pc, pd, step, viol;\n"
      "  initial begin\n"
      "    viol = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0;\n"
      "      randsequence(main)\n"
      "        main : rand join s1 s2;\n"
      "        s1 : a b;\n"
      "        s2 : c d;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        b : { pb = step; step = step + 1; };\n"
      "        c : { pc = step; step = step + 1; };\n"
      "        d : { pd = step; step = step + 1; };\n"
      "      endsequence\n"
      "      if (!(pa < pb && pc < pd)) viol = viol + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "viol");
  EXPECT_EQ(viol, 0u);
}

// 18.17.5: rand join actually interleaves the sequences rather than running one
// after the other. Over many runs at the neutral default, orders where the two
// sequences overlap (neither fully precedes the other) occur, and so do the two
// fully blocked orders, proving the generator mixes them.
TEST(RandsequenceSim, RandJoinInterleavesSequences) {
  const char* src =
      "module t;\n"
      "  int pa, pb, pc, pd, step, mixed;\n"
      "  initial begin\n"
      "    mixed = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0;\n"
      "      randsequence(main)\n"
      "        main : rand join s1 s2;\n"
      "        s1 : a b;\n"
      "        s2 : c d;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        b : { pb = step; step = step + 1; };\n"
      "        c : { pc = step; step = step + 1; };\n"
      "        d : { pd = step; step = step + 1; };\n"
      "      endsequence\n"
      "      if (!(pb < pc) && !(pd < pa)) mixed = mixed + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t mixed = RunAndRead(src, "mixed");
  // Interleaved orders dominate but blocked orders still appear, so the count
  // sits strictly between none and all of the runs.
  EXPECT_GT(mixed, 0u);
  EXPECT_LT(mixed, 300u);
}

// 18.17.5: the weight expression controls how the remaining length of each
// sequence biases selection. With a short (length 1) and a long (length 3)
// operand, a weight of 0.0 favors the short sequence so its single production
// leads most often, 1.0 favors the long sequence so it leads least often, and
// 0.5 sits in between.
TEST(RandsequenceSim, RandJoinLengthBiasDirection) {
  const char* tmpl =
      "module t;\n"
      "  int pa, step, af0, af05, af1;\n"
      "  initial begin\n"
      "    af0 = 0; af05 = 0; af1 = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (0.0) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) af0 = af0 + 1;\n"
      "    end\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (0.5) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) af05 = af05 + 1;\n"
      "    end\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (1.0) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) af1 = af1 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t af0 = RunAndRead(tmpl, "af0");
  uint64_t af05 = RunAndRead(tmpl, "af05");
  uint64_t af1 = RunAndRead(tmpl, "af1");
  // Short favored most at 0.0, least at 1.0, with 0.5 strictly in between.
  EXPECT_GT(af0, af05 + 30u);
  EXPECT_GT(af05, af1 + 20u);
  EXPECT_GT(af0, 150u);
  EXPECT_LT(af1, 60u);
}

// 18.17.5: when the weight expression is omitted the generator uses 0.5, so an
// absent weight produces the same length bias as an explicit 0.5.
TEST(RandsequenceSim, RandJoinDefaultWeightIsHalf) {
  const char* tmpl =
      "module t;\n"
      "  int pa, step, afdef, afhalf;\n"
      "  initial begin\n"
      "    afdef = 0; afhalf = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afdef = afdef + 1;\n"
      "    end\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (0.5) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afhalf = afhalf + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t afdef = RunAndRead(tmpl, "afdef");
  uint64_t afhalf = RunAndRead(tmpl, "afhalf");
  int64_t diff = static_cast<int64_t>(afdef) - static_cast<int64_t>(afhalf);
  if (diff < 0) diff = -diff;
  EXPECT_LT(diff, 40);
}

// 18.17.5: the weight shall be a real number in [0.0, 1.0]. A value below the
// range is clamped to 0.0, so it produces the same bias as an explicit 0.0
// rather than an ever stronger preference for the short sequence.
TEST(RandsequenceSim, RandJoinWeightClampedToRange) {
  const char* tmpl =
      "module t;\n"
      "  int pa, step, afzero, afneg;\n"
      "  initial begin\n"
      "    afzero = 0; afneg = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (0.0) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afzero = afzero + 1;\n"
      "    end\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (-5.0) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afneg = afneg + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t afzero = RunAndRead(tmpl, "afzero");
  uint64_t afneg = RunAndRead(tmpl, "afneg");
  // Clamped to 0.0: still favors the short sequence, but not saturated the way
  // an unclamped negative exponent would make it.
  EXPECT_GT(afneg, 150u);
  EXPECT_LT(afneg, 280u);
  int64_t diff = static_cast<int64_t>(afzero) - static_cast<int64_t>(afneg);
  if (diff < 0) diff = -diff;
  EXPECT_LT(diff, 50);
}

// 18.17.5: the weight shall be a real number in [0.0, 1.0]. A value above the
// range is clamped to 1.0, so it produces the same long-sequence preference as
// an explicit 1.0 instead of a runaway exaggeration of it. Lengths 2 and 3 keep
// the clamped bias well clear of zero so the clamp is observable: without it a
// weight of 5.0 would drive the short sequence to lead almost never.
TEST(RandsequenceSim, RandJoinWeightClampedToHighBound) {
  const char* tmpl =
      "module t;\n"
      "  int pa, step, afone, afhigh;\n"
      "  initial begin\n"
      "    afone = 0; afhigh = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (1.0) s1 s2;\n"
      "        s1 : a b;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        b : { step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afone = afone + 1;\n"
      "    end\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (5.0) s1 s2;\n"
      "        s1 : a b;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        b : { step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) afhigh = afhigh + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t afone = RunAndRead(tmpl, "afone");
  uint64_t afhigh = RunAndRead(tmpl, "afhigh");
  // Clamped to 1.0: the short sequence still leads a noticeable fraction of the
  // time, matching an explicit 1.0 rather than collapsing toward zero.
  EXPECT_GT(afhigh, 30u);
  int64_t diff = static_cast<int64_t>(afone) - static_cast<int64_t>(afhigh);
  if (diff < 0) diff = -diff;
  EXPECT_LT(diff, 40);
}

// 18.17.5: rand join interleaves two or more sequences. With three operands the
// generator still preserves the relative order inside each one (a before b, c
// before d, e before f) and always emits every production.
TEST(RandsequenceSim, RandJoinInterleavesThreeSequences) {
  const char* src =
      "module t;\n"
      "  int pa, pb, pc, pd, pe, pf, step, viol, allran;\n"
      "  initial begin\n"
      "    viol = 0; allran = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0;\n"
      "      pa = 99; pb = 99; pc = 99; pd = 99; pe = 99; pf = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join s1 s2 s3;\n"
      "        s1 : a b;\n"
      "        s2 : c d;\n"
      "        s3 : e f;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        b : { pb = step; step = step + 1; };\n"
      "        c : { pc = step; step = step + 1; };\n"
      "        d : { pd = step; step = step + 1; };\n"
      "        e : { pe = step; step = step + 1; };\n"
      "        f : { pf = step; step = step + 1; };\n"
      "      endsequence\n"
      "      if (!(pa < pb && pc < pd && pe < pf)) viol = viol + 1;\n"
      "      if (step == 6) allran = allran + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t viol = RunAndRead(src, "viol");
  uint64_t allran = RunAndRead(src, "allran");
  EXPECT_EQ(viol, 0u);
  EXPECT_EQ(allran, 300u);
}

}  // namespace
