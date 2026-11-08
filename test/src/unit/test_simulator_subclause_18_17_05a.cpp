#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

uint64_t ReadAfterRun(SimFixture& f, const char* var_name) {
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  return var ? var->value.ToUint64() : 0;
}

constexpr const char* kOutsideTheRange =
    "rand join expression lies outside 0.0 to 1.0; it needs a real number in "
    "that range";

uint64_t RunAndRead(const char* src, const char* var_name, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return ReadAfterRun(f, var_name);
}

uint64_t RunAndRead(const char* src, const char* var_name) {
  SimFixture f;
  return RunAndRead(src, var_name, f);
}

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
  EXPECT_GT(mixed, 0u);
  EXPECT_LT(mixed, 300u);
}

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
  EXPECT_GT(af0, af05 + 30u);
  EXPECT_GT(af05, af1 + 20u);
  EXPECT_GT(af0, 150u);
  EXPECT_LT(af1, 60u);
}

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
  SimFixture f;
  uint64_t afzero = RunAndRead(tmpl, "afzero", f);
  uint64_t afneg = ReadAfterRun(f, "afneg");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kOutsideTheRange, 21, "18.17.5"));
  EXPECT_GT(afneg, 150u);
  EXPECT_LT(afneg, 280u);
  int64_t diff = static_cast<int64_t>(afzero) - static_cast<int64_t>(afneg);
  if (diff < 0) diff = -diff;
  EXPECT_LT(diff, 50);
}

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
  SimFixture f;
  uint64_t afone = RunAndRead(tmpl, "afone", f);
  uint64_t afhigh = ReadAfterRun(f, "afhigh");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kOutsideTheRange, 22, "18.17.5"));
  EXPECT_GT(afhigh, 30u);
  int64_t diff = static_cast<int64_t>(afone) - static_cast<int64_t>(afhigh);
  if (diff < 0) diff = -diff;
  EXPECT_LT(diff, 40);
}

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

TEST(RandsequenceSim, RandJoinInterleavesToDepthOne) {
  const char* src =
      "module t;\n"
      "  int pp, pq, step, viol, mid;\n"
      "  initial begin\n"
      "    viol = 0; mid = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pp = 99; pq = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d;\n"
      "        a : p q;\n"
      "        p : { pp = step; step = step + 1; };\n"
      "        q : { pq = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pq != pp + 1) viol = viol + 1;\n"
      "      if (pp > 0) mid = mid + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t viol = RunAndRead(src, "viol");
  uint64_t mid = RunAndRead(src, "mid");
  EXPECT_EQ(viol, 0u);
  EXPECT_GT(mid, 0u);
}

TEST(RandsequenceSim, RandJoinWeightFromParameter) {
  uint64_t af0 = RunAndRead(
      "module t;\n"
      "  parameter real BIAS = 0.0;\n"
      "  int pa, step, af0;\n"
      "  initial begin\n"
      "    af0 = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (BIAS) s1 s2;\n"
      "        s1 : a;\n"
      "        s2 : c d e;\n"
      "        a : { pa = step; step = step + 1; };\n"
      "        c : { step = step + 1; };\n"
      "        d : { step = step + 1; };\n"
      "        e : { step = step + 1; };\n"
      "      endsequence\n"
      "      if (pa == 0) af0 = af0 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "af0");
  EXPECT_GT(af0, 150u);
}

TEST(RandsequenceSim, RandJoinWeightFromLocalparam) {
  uint64_t af1 = RunAndRead(
      "module t;\n"
      "  localparam real BIAS = 1.0;\n"
      "  int pa, step, af1;\n"
      "  initial begin\n"
      "    af1 = 0;\n"
      "    repeat (300) begin\n"
      "      step = 0; pa = 99;\n"
      "      randsequence(main)\n"
      "        main : rand join (BIAS) s1 s2;\n"
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
      "endmodule\n",
      "af1");
  EXPECT_LT(af1, 60u);
}

TEST(RandsequenceSim, RandJoinElementsFollowSyntacticOrderNotGenerationOrder) {
  SimFixture f;
  auto [bad, swapped] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int p;\n"
      "  int n, first, second, bad, swapped;\n"
      "  initial begin\n"
      "    p = 0; bad = 0; swapped = 0;\n"
      "    repeat (300) begin\n"
      "      n = 0; first = 0; second = 0;\n"
      "      randsequence(main)\n"
      "        void main : rand join p p\n"
      "                    := 1 { first = p[1]; second = p[2]; };\n"
      "        int p : { n = n + 1; return n; };\n"
      "      endsequence\n"
      "      if (!((first == 1 && second == 2) ||\n"
      "            (first == 2 && second == 1))) bad = bad + 1;\n"
      "      if (first == 2) swapped = swapped + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "bad", "swapped");
  EXPECT_EQ(bad, 0u);
  EXPECT_GT(swapped, 0u);
  EXPECT_LT(swapped, 300u);
}

}  // namespace
