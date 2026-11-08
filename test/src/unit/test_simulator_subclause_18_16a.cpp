#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void RunThreeWeightRandcase(SimFixtureSeeded& f, std::string_view decls,
                            std::string_view weight, uint64_t& cnt,
                            uint64_t& x) {
  std::string w(weight);
  std::string src =
      "module t;\n"
      "  int unsigned cnt;\n"
      "  int unsigned x;\n" +
      std::string(decls) +
      "  initial begin\n"
      "    cnt = 0;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      " +
      w + " : x = 1;\n      " + w + " : x = 2;\n      " + w +
      " : x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  cnt = f.ctx.FindVariable("cnt")->value.ToUint64();
  x = f.ctx.FindVariable("x")->value.ToUint64();
}

TEST(RandcaseWeightedCase, WeightExpressionsEvaluatedAtMostOnce) {
  SimFixtureSeeded f;
  uint64_t cnt = 0;
  uint64_t x = 0;
  RunThreeWeightRandcase(f, "", "(cnt++ + 1)", cnt, x);
  EXPECT_EQ(cnt, 3u);
  EXPECT_GE(x, 1u);
  EXPECT_LE(x, 3u);
}

TEST(RandcaseWeightedCase, FunctionCallWeightEvaluatedOncePerBranch) {
  SimFixtureSeeded f;
  uint64_t cnt = 0;
  uint64_t x = 0;
  RunThreeWeightRandcase(f,
                         "  function int bump();\n"
                         "    cnt = cnt + 1;\n"
                         "    return 1;\n"
                         "  endfunction\n",
                         "(bump())", cnt, x);
  EXPECT_EQ(cnt, 3u);
  EXPECT_GE(x, 1u);
  EXPECT_LE(x, 3u);
}

TEST(RandcaseWeightedCase, SingleNonzeroWeightAmongZerosAlwaysSelected) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      0 : x = 1;\n"
      "      0 : x = 2;\n"
      "      5 : x = 3;\n"
      "      0 : x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 3u);
}

TEST(RandcaseWeightedCase, AllZeroWeightsTakesNoBranchAndWarns) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 99;\n"
      "    randcase\n"
      "      0 : x = 1;\n"
      "      0 : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 99u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(RandcaseWeightedCase, WeightsCanBeArbitraryExpressions) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a, b;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    a = 8'd6;\n"
      "    b = 8'd2;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      a + b   : x = 1;\n"
      "      a - b   : x = 2;\n"
      "      a ^ ~b  : x = 3;\n"
      "      12'h800 : x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto x = f.ctx.FindVariable("x")->value.ToUint64();
  EXPECT_GE(x, 1u);
  EXPECT_LE(x, 4u);
}

TEST(RandcaseWeightedCase, NegativeSignedWeightCountsAsUnsigned) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte w;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    w = -1;\n"
      "    x = 0;\n"
      "    randcase\n"
      "      w : x = 7;\n"
      "      0 : x = 8;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 7u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(RandcaseWeightedCase, BranchFrequenciesTrackWeightProbabilities) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned c1, c2, c3;\n"
      "  int i;\n"
      "  initial begin\n"
      "    c1 = 0; c2 = 0; c3 = 0;\n"
      "    for (i = 0; i < 8000; i = i + 1) begin\n"
      "      randcase\n"
      "        3 : c1 = c1 + 1;\n"
      "        1 : c2 = c2 + 1;\n"
      "        4 : c3 = c3 + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto c1 = f.ctx.FindVariable("c1")->value.ToUint64();
  auto c2 = f.ctx.FindVariable("c2")->value.ToUint64();
  auto c3 = f.ctx.FindVariable("c3")->value.ToUint64();
  EXPECT_EQ(c1 + c2 + c3, 8000u);
  EXPECT_NEAR(static_cast<double>(c1) / 8000.0, 0.375, 0.05);
  EXPECT_NEAR(static_cast<double>(c2) / 8000.0, 0.125, 0.05);
  EXPECT_NEAR(static_cast<double>(c3) / 8000.0, 0.500, 0.05);
}

TEST(RandcaseWeightedCase, SumWiderThan32BitsCoversFullRange) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned lo_cnt, hi_cnt;\n"
      "  int i;\n"
      "  initial begin\n"
      "    lo_cnt = 0; hi_cnt = 0;\n"
      "    for (i = 0; i < 200; i = i + 1) begin\n"
      "      randcase\n"
      "        64'h100000000 : lo_cnt = lo_cnt + 1;\n"
      "        64'h100000000 : hi_cnt = hi_cnt + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto lo_cnt = f.ctx.FindVariable("lo_cnt")->value.ToUint64();
  auto hi_cnt = f.ctx.FindVariable("hi_cnt")->value.ToUint64();
  EXPECT_EQ(lo_cnt + hi_cnt, 200u);
  EXPECT_GT(hi_cnt, 0u);
  EXPECT_GT(lo_cnt, 0u);
}

TEST(RandcaseWeightedCase, WeightPrecisionIsSelfDetermined) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned narrow_hits, wide_hits;\n"
      "  int i;\n"
      "  initial begin\n"
      "    narrow_hits = 0; wide_hits = 0;\n"
      "    for (i = 0; i < 500; i = i + 1) begin\n"
      "      randcase\n"
      "        (4'd8 + 4'd8) : narrow_hits = narrow_hits + 1;\n"
      "        32'd1000      : wide_hits = wide_hits + 1;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("narrow_hits")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("wide_hits")->value.ToUint64(), 500u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(RandcaseWeightedCase, ParameterValuedWeightIsUsed) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P_W = 5;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      P_W : x = 1;\n"
      "      0   : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(RandcaseWeightedCase, LocalparamValuedWeightIsUsed) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int L_W = 4;\n"
      "  int unsigned x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randcase\n"
      "      L_W : x = 1;\n"
      "      0   : x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(RandcaseWeightedCase, SelectionDrawsFromSeedableUrandomStream) {
  const char* src =
      "module t;\n"
      "  int sig_a, sig_b, sig_c;\n"
      "  int i, sel;\n"
      "  initial begin\n"
      "    automatic process pr = process::self();\n"
      "    pr.srandom(555);\n"
      "    sig_a = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_a = sig_a * 7 + sel;\n"
      "    end\n"
      "    pr.srandom(555);\n"
      "    sig_b = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_b = sig_b * 7 + sel;\n"
      "    end\n"
      "    pr.srandom(999);\n"
      "    sig_c = 0;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      sel = 0;\n"
      "      randcase\n"
      "        1 : sel = 1;\n"
      "        2 : sel = 2;\n"
      "        3 : sel = 3;\n"
      "      endcase\n"
      "      sig_c = sig_c * 7 + sel;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto a = f.ctx.FindVariable("sig_a")->value.ToUint64();
  auto b = f.ctx.FindVariable("sig_b")->value.ToUint64();
  auto c = f.ctx.FindVariable("sig_c")->value.ToUint64();
  EXPECT_EQ(a, b);
  EXPECT_NE(a, c);
}

TEST(RandcaseWeightedCase, AllZeroWeightsWarningNames18_16) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned y;\n"
      "  initial begin\n"
      "    y = 5;\n"
      "    randcase\n"
      "      0 : y = 6;\n"
      "      0 : y = 7;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "randcase: all weights are zero", 5, "18.16"));
}

TEST(RandcaseWeightedCase, WeightsSummingPastThirtyTwoBitsReachEveryBranch) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned n1, n2;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    n1 = 0; n2 = 0;\n"
      "    for (i = 0; i < 40; i = i + 1)\n"
      "      randcase\n"
      "        64'h1_0000_0000 : n1 = n1 + 1;\n"
      "        64'h1_0000_0000 : n2 = n2 + 1;\n"
      "      endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GT(f.ctx.FindVariable("n1")->value.ToUint64(), 0u);
  EXPECT_GT(f.ctx.FindVariable("n2")->value.ToUint64(), 0u);
}

}  // namespace
