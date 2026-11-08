#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

bool AllBitsX(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != ~uint64_t{0}) return false;
    if (v.words[w].bval != ~uint64_t{0}) return false;
  }
  return true;
}

TEST(ChargeDecayProcess, StoredOneDecaysToXAfterDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

TEST(ChargeDecayProcess, StoredZeroDecaysToXAfterDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 25) cap;\n"
      "  assign cap = en ? 64'd0 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

TEST(ChargeDecayProcess, WideVectorDecaysEveryBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [127:0] #(0, 0, 45) cap;\n"
      "  assign cap = en ? 128'd1 : 128'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

TEST(ChargeDecayProcess, ContinuouslyDrivenTriregNeverDecays) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg [63:0] #(0, 0, 5) cap;\n"
      "  assign cap = 64'd1;\n"
      "  initial #40;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(cap->InCapacitiveState());
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, DriverTurningOnPropagatingZeroEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd1; en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #5;\n"
      "    val = 64'd0; en = 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, DriverTurningOnPropagatingOneEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd0; en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #5;\n"
      "    val = 64'd1; en = 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, DriverTurningOnPropagatingXEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd0; en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #5;\n"
      "    val = 64'bx; en = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(cap->InCapacitiveState());
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

static Net* RunTriregDecayUntil(const char* finish_stmt, SimFixture& f) {
  std::string src =
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n";
  src += finish_stmt;
  src +=
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  return f.ctx.FindNet("cap");
}

TEST(ChargeDecayProcess, StoredValueIntactBeforeDelayElapses) {
  SimFixture f;
  auto* cap = RunTriregDecayUntil("    #10 $finish;\n", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, StoredValueHasDecayedAfterDelayElapses) {
  SimFixture f;
  auto* cap = RunTriregDecayUntil("    #100 $finish;\n", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

TEST(ChargeDecayProcess, NoChargeDecayTimeMeansStoredValueNeverDecays) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, DecayedChargeReportsItsXStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  logic data, gate;\n"
      "  trireg (large) #(0, 0, 50) cap1;\n"
      "  nmos nmos1 (cap1, data, gate);\n"
      "  initial begin\n"
      "    data = 1; gate = 1;\n"
      "    #10 gate = 0;\n"
      "    #1 $display(\"t=%0t cap1=%b %v\", $time, cap1, cap1);\n"
      "    #48 $display(\"t=%0t cap1=%b %v\", $time, cap1, cap1);\n"
      "    #2 $display(\"t=%0t cap1=%b %v\", $time, cap1, cap1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=11 cap1=1 La1\n"
            "t=59 cap1=1 La1\n"
            "t=61 cap1=x LaX\n");
}

TEST(ChargeDecayProcess, ADriverReCommittingZDoesNotRestartTheDecay) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg en = 1, d = 1;\n"
      "  trireg #(0, 0, 50) t;\n"
      "  bufif1 g (t, d, en);\n"
      "  initial begin\n"
      "    #10 en = 0;\n"
      "    #30 d = 0;\n"
      "    #30 $display(\"%b\", t);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

TEST(ChargeDecayProcess, ADriverTheChargeOutranksDoesNotEndTheDecay) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg en1 = 1, en2 = 0;\n"
      "  trireg (large) #(0, 0, 50) t;\n"
      "  bufif1 (strong0, strong1) g1 (t, 1'b1, en1);\n"
      "  bufif1 (weak0, weak1) g2 (t, 1'b0, en2);\n"
      "  initial begin\n"
      "    #10 en1 = 0;\n"
      "    #10 en2 = 1;\n"
      "    #30 $display(\"%b\", t);\n"
      "    #20 $display(\"%b\", t);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "1\n"
            "x\n");
}

}  // namespace
