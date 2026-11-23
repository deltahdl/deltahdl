#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "parser/ast_specify.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefSim, RuntimeTimingCheckEntryEdges) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.data_edge = SpecifyEdge::kNone;
  tc.limit = 10;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(mgr.GetTimingChecks()[0].data_edge, SpecifyEdge::kNone);
}

TEST(TimingCheckEventDefSim, TerminalBitSelectSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TimingCheckEventDefSim, TerminalPartSelectSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data[3:0], posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd88;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(TimingCheckEventDefSim, ControlledTimingCheckEventPeriodSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TimingCheckEventDefSim, RuntimeTimingCheckEntryNegedge) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kNegedge;
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].ref_edge, SpecifyEdge::kNegedge);
}

bool SetupFiresUnder(const std::string& condition, const std::string& width,
                     const std::string& value) {
  SimFixture f;
  auto* rtl = ElaborateSrc(
      "module top(output logic d, output logic clk);\n"
      "  logic " +
          width +
          " e;\n"
          "  wire " +
          width +
          " en = e;\n"
          "  specify\n"
          "    $setup(d, posedge clk &&& (" +
          condition +
          "), 29);\n"
          "  endspecify\n"
          "  initial begin\n"
          "    d = 1'b0;\n"
          "    clk = 1'b0;\n"
          "    e = " +
          value +
          ";\n"
          "    #13 d = 1'b1;\n"
          "    #6 clk = 1'b1;\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(rtl, nullptr) << condition;
  EXPECT_FALSE(f.has_errors) << condition;
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("$setup violation: data signal") != std::string::npos) {
      return true;
    }
  }
  return false;
}

TEST(TimingCheckEventDefSim,
     AOneBitLiteralOutsideTheScalarConstantsIsAPlainCondition) {
  EXPECT_TRUE(SetupFiresUnder("en == 1'b1", "", "1'bx"));
  EXPECT_FALSE(SetupFiresUnder("en == 1'h1", "", "1'bx"));
  EXPECT_FALSE(SetupFiresUnder("en == 1'd1", "", "1'bx"));
  EXPECT_TRUE(SetupFiresUnder("en == 1'h1", "", "1'b1"));
}

TEST(TimingCheckEventDefSim, AnUnknownLiteralOperandDisablesTheCheck) {
  EXPECT_FALSE(SetupFiresUnder("en == 1'bx", "", "1'b1"));
  EXPECT_FALSE(SetupFiresUnder("en == 1'bz", "", "1'b1"));
  EXPECT_TRUE(SetupFiresUnder("en == 1'b1", "", "1'b1"));
}

TEST(TimingCheckEventDefSim, ADecimalOtherThanZeroOrOneIsComparedWhole) {
  EXPECT_TRUE(SetupFiresUnder("en == 2", "[1:0]", "2'b10"));
  EXPECT_FALSE(SetupFiresUnder("en == 2", "[1:0]", "2'b11"));
}

}  // namespace
