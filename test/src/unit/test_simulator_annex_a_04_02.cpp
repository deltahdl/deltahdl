#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GenerateSimulation, GenerateForAssignValues) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t #(parameter N = 3) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 10;\n"
      "    end\n"
      "  endgenerate\n"
      "  assign x = 7;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(GenerateSimulation, EachIterationOperatorStepsTheGenvarByItsOwnOperation) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  genvar a, b, c, d, e, g, h, k, l, n;\n"
      "  wire [64:0] ha, hb, hc, hd, he, hg, hh, hk, hl, hn;\n"
      "  for (a = 64; a > 0; a -= 8) assign ha[a] = 1'b1;\n"
      "  for (b = 64; b > 1; b /= 2) assign hb[b] = 1'b1;\n"
      "  for (c = 13; c > 1; c %= 4) assign hc[c] = 1'b1;\n"
      "  for (d = 7; d > 1; d &= 1) assign hd[d] = 1'b1;\n"
      "  for (e = 1; e < 8; e |= e << 1) assign he[e] = 1'b1;\n"
      "  for (g = 1; g < 16; g ^= g << 1) assign hg[g] = 1'b1;\n"
      "  for (h = 1; h < 16; h <<= 1) assign hh[h] = 1'b1;\n"
      "  for (k = 16; k > 0; k >>= 1) assign hk[k] = 1'b1;\n"
      "  for (l = 1; l < 40; l <<<= 2) assign hl[l] = 1'b1;\n"
      "  for (n = 48; n > 0; n >>>= 2) assign hn[n] = 1'b1;\n"
      "  task automatic show(input logic [64:0] v);\n"
      "    for (int i = 0; i <= 64; i++)\n"
      "      if (v[i] === 1'b1) $write(\" %0d\", i);\n"
      "    $write(\"\\n\");\n"
      "  endtask\n"
      "  initial begin\n"
      "    #1;\n"
      "    show(ha); show(hb); show(hc); show(hd); show(he);\n"
      "    show(hg); show(hh); show(hk); show(hl); show(hn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            " 8 16 24 32 40 48 56 64\n"
            " 2 4 8 16 32 64\n"
            " 13\n"
            " 7\n"
            " 1 3 7\n"
            " 1 3 5 15\n"
            " 1 2 4 8\n"
            " 1 2 4 8 16\n"
            " 1 4 16\n"
            " 3 12 48\n");
}

}  // namespace
