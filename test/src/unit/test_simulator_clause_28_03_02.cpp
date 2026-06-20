#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(HighzStrengthOutput, Highz1ProducesZWhenGateComputesOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(HighzStrengthOutput, Highz0ProducesZWhenGateComputesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b1; end\n"
      "  and (highz0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(HighzStrengthOutput, Highz1DoesNotAffectZeroOutput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b1; end\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(Strength01Semantics, Strength0AndStrength1ReachNetDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  and (pull0, supply1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_FALSE(net->driver_strengths.empty());
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kPull);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kSupply);
}

}  // namespace
