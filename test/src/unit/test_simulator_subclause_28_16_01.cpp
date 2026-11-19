#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

uint64_t SettleTicksUnderMode(const std::string& src, DelayMode mode) {
  SimFixture f;
  f.ctx.SetDelayMode(mode);
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return 0;
  LowerAndRun(design, f);
  return f.scheduler.CurrentTime().ticks;
}

TEST(MinTypMaxDelaySim, GateRiseDelayTripleSelectsTheMemberForTheMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(7:11:15) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b1; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 107u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 111u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 115u);
}

TEST(MinTypMaxDelaySim, TurnOffSlotCarriesItsOwnTriple) {
  const std::string kSrc =
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(5:7:9, 8:10:12, 15:18:21) g(y, d, en);\n"
      "  initial begin d = 1'b1; en = 1'b1; #100 en = 1'b0; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 115u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 121u);
}

TEST(MinTypMaxDelaySim, NetDeclarationDelayTripleSelectsByMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a;\n"
      "  wire #(3:5:7) y = a;\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

TEST(MinTypMaxDelaySim, ContinuousAssignmentDelayTripleSelectsByMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  assign #(3:5:7) y = a;\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

TEST(MinTypMaxDelaySim, UnorderedTripleIsUsedAsWritten) {
  const std::string kSrc =
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(15:11:7) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b1; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 115u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

TEST(MinTypMaxDelaySim, ProceduralDelayTripleTakesParameterMembers) {
  const std::string kSrc =
      "module m;\n"
      "  parameter min_hi = 97, typ_hi = 100, max_hi = 107;\n"
      "  reg clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #(min_hi:typ_hi:max_hi) clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 97u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 100u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

bool Bit0IsX(const Logic4Vec& v) {
  return (v.words[0].aval & 1u) == 1u && (v.words[0].bval & 1u) == 1u;
}

bool TriregDecayedBy(const char* finish_stmt) {
  SimFixture f;
  std::string src =
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 20:40:60) cap;\n"
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
  if (design == nullptr) return false;
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindNet("cap");
  EXPECT_NE(cap, nullptr);
  if (cap == nullptr) return false;
  return Bit0IsX(cap->resolved->value);
}

TEST(MinTypMaxDelaySim, TriregChargeDecayTimeTripleDecaysAtTheTypicalMember) {
  EXPECT_FALSE(TriregDecayedBy("    #30 $finish;\n"));
  EXPECT_TRUE(TriregDecayedBy("    #50 $finish;\n"));
}

TEST(MinTypMaxDelaySim, UdpInstanceDelayTripleSelectsByMode) {
  const std::string kSrc =
      "primitive p(output y, input a);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  p #(3:5:7, 4:6:8) u(y, a);\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 105u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

TEST(MinTypMaxDelaySim, NetDelayTripleTimesASeparateContinuousAssignment) {
  const std::string kSrc =
      "module m;\n"
      "  reg a;\n"
      "  wire #(3:5:7, 11) y;\n"
      "  assign y = a;\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 105u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

std::string TriregDecaySamplesUnderMode(DelayMode mode) {
  DelayModeGuard guard(mode);
  SimFixture f;
  f.ctx.SetDelayMode(mode);
  return RunCapture(
      "module m;\n"
      "  reg en;\n"
      "  trireg #(0, 0, 20:40:60) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1; #100 en = 0;\n"
      "    #19 $write(\"%b\", cap); #2 $write(\"%b\", cap);\n"
      "    #18 $write(\"%b\", cap); #2 $write(\"%b\", cap);\n"
      "    #18 $write(\"%b\", cap); #2 $display(\"%b\", cap);\n"
      "  end\n"
      "endmodule\n",
      f);
}

TEST(MinTypMaxDelaySim, TriregChargeDecayTripleSelectsEveryMemberByMode) {
  EXPECT_EQ(TriregDecaySamplesUnderMode(DelayMode::kMin), "1xxxxx\n");
  EXPECT_EQ(TriregDecaySamplesUnderMode(DelayMode::kTyp), "111xxx\n");
  EXPECT_EQ(TriregDecaySamplesUnderMode(DelayMode::kMax), "11111x\n");
}

}  // namespace
