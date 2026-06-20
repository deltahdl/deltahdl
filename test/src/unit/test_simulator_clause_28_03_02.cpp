#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs an `and` gate with the given initial input assignments and strength
// spec, then verifies the resolved value's low aval/bval bits on net `y`.
void RunAndCheckResolvedWord(const std::string& initial_line,
                             const std::string& gate_line, uint32_t expect_aval,
                             uint32_t expect_bval) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string("module top;\n"
                                          "  logic a, b;\n"
                                          "  wire y;\n") +
                                  initial_line + gate_line + "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, expect_aval);
  EXPECT_EQ(w.bval & 1u, expect_bval);
}

TEST(HighzStrengthOutput, Highz1ProducesZWhenGateComputesOne) {
  RunAndCheckResolvedWord("  initial begin a = 1'b1; b = 1'b1; end\n",
                          "  and (strong0, highz1) g1(y, a, b);\n", 1u, 1u);
}

TEST(HighzStrengthOutput, Highz0ProducesZWhenGateComputesZero) {
  RunAndCheckResolvedWord("  initial begin a = 1'b0; b = 1'b1; end\n",
                          "  and (highz0, strong1) g1(y, a, b);\n", 1u, 1u);
}

TEST(HighzStrengthOutput, Highz1DoesNotAffectZeroOutput) {
  RunAndCheckResolvedWord("  initial begin a = 1'b0; b = 1'b1; end\n",
                          "  and (strong0, highz1) g1(y, a, b);\n", 0u, 0u);
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
